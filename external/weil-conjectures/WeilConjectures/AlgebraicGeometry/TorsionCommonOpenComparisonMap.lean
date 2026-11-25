/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentCompletionOverNormalization
import WeilConjectures.AlgebraicGeometry.TorsionLocalModelRestriction
import WeilConjectures.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A prescribed completed comparison lifts to a map on any common open.
Only a map is asserted: invertibility and all cocycle identities are consequences
of section separation, proved in the parent module.
Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness.
(blueprint: lem-weil-pbc-torsion-common-open-comparison-map).

Proof: Transfer Li and Lj through overEquiv and restrict Fi, Fj and H to W.
Coherence, kernels, cokernels and their ideal-power annihilation bounds restrict
along these open immersions. Use the normalized quotient restriction comparison
and beta_i, beta_j to identify their completions with N restricted to W.
The prescribed completed map is beta_i inverse followed by beta_j, with those
restriction comparisons. The equations hdelta show it commutes with the maps to
the completion of H: precompose each component with the quotient epimorphism
and use hqi and hbi. Apply torsionControlled_completion_hom_lift_exists on W.
Transfer the resulting map back through overEquiv. Its equation over H yields
the b equation on each V contained in W. Its completed equation, precomposed
with the source quotient projection and rewritten using hqi, yields the q
equations. This uses arbitrary open restrictions, not affine intersections.
For J=0 the completed comparison is the original map. For J=1 both arrows to
H are isomorphisms and the comparison is their composite. On an empty common
open the unique map suffices; the index type may also be empty.
-/
theorem torsion_common_open_comparison_map
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ai : ∀ i, Fi i ⟶ Hlocal i)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (hbound : ∀ i, ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel (ai i).hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel (ai i).hom)))
    (Li : ∀ i, SheafOfModules ((moduleRings X.toRingedSpace).over (U i)))
    (li : ∀ i, (Scheme.Modules.overEquiv (U i)).functor.obj (Li i) ≅ (Fi i).obj)
    (bi : ∀ i, Li i ⟶ H.obj.over (U i))
    (qi : ∀ (i : ι) (n : ℕᵒᵖ), Li i ⟶ (N.obj.obj n).over (U i))
    (hbi : (∀ i, (Scheme.Modules.overEquiv (U i)).functor.map (bi i) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj ≫
          eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom))
    (hqi : (∀ (i : ι) (n : ℕᵒᵖ), (Scheme.Modules.overEquiv (U i)).functor.map (qi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
          (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
            (βi i).inv.app n))
    (hδ : (∀ (i : ι) (n : ℕᵒᵖ), qi i n ≫ (δ.hom.app n).over (U i) =
        bi i ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)))
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    ∃ f : (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hi : W ⟶ U i)).obj (Li i) ⟶
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hj : W ⟶ U j)).obj (Li j),
      (∀ (V : X.Opens) (hV : V ≤ W),
        f.val.app (op (Over.mk (homOfLE hV))) ≫
          (bi j).val.app (op (Over.mk (homOfLE (hV.trans hj)))) =
            (bi i).val.app (op (Over.mk (homOfLE (hV.trans hi))))) ∧
      (∀ (n : ℕᵒᵖ) (V : X.Opens) (hV : V ≤ W),
        f.val.app (op (Over.mk (homOfLE hV))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE (hV.trans hj)))) =
            (qi i n).val.app (op (Over.mk (homOfLE (hV.trans hi))))) := by
  classical
  have : TopologicalSpace.NoetherianSpace W.toScheme :=
    (Scheme.Hom.isOpenEmbedding W.ι).isInducing.noetherianSpace
  let : IsNoetherian W.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let E := (Scheme.Modules.overEquiv W).functor
  let R := moduleRings X.toRingedSpace
  let Ti := SheafOfModules.overMap R (homOfLE hi : W ⟶ U i)
  let Tj := SheafOfModules.overMap R (homOfLE hj : W ⟶ U j)
  let bwi := Ti.map (bi i) ≫
    (SheafOfModules.overFunctorMap R (homOfLE hi : W ⟶ U i)).hom.app H.obj
  let bwj := Tj.map (bi j) ≫
    (SheafOfModules.overFunctorMap R (homOfLE hj : W ⟶ U j)).hom.app H.obj
  let qwi (n : ℕᵒᵖ) := Ti.map (qi i n) ≫
    (SheafOfModules.overFunctorMap R (homOfLE hi : W ⟶ U i)).hom.app (N.obj.obj n)
  let qwj (n : ℕᵒᵖ) := Tj.map (qi j n) ≫
    (SheafOfModules.overFunctorMap R (homOfLE hj : W ⟶ U j)).hom.app (N.obj.obj n)
  obtain ⟨hHw, c, hc⟩ := coherentCompletion_over_normalization J H W
  let Hw : CoherentModules W.toScheme := ⟨E.obj (H.obj.over W), hHw⟩
  obtain ⟨F, lF, a, βF, ha, hbF, hqF⟩ :=
    torsionLocalModel_restriction J H N (U i) W hi (Hlocal i) (Fi i)
      (hHlocal i) (ai i) (βi i) (hbound i) (Li i) (li i) (bi i) (qi i)
      (hbi i) (hqi i) Hw rfl
  obtain ⟨G, lG, a', βG, ha', hbG, hqG⟩ :=
    torsionLocalModel_restriction J H N (U j) W hj (Hlocal j) (Fi j)
      (hHlocal j) (ai j) (βi j) (hbound j) (Li j) (li j) (bi j) (qi j)
      (hbi j) (hqi j) Hw rfl
  have hbF' : E.map bwi = lF.hom ≫ a.hom := by
    simpa only [eqToHom_refl, Category.comp_id] using hbF
  have hbG' : E.map bwj = lG.hom ≫ a'.hom := by
    simpa only [eqToHom_refl, Category.comp_id] using hbG
  let d := Functor.whiskerRight (Functor.whiskerRight δ.hom
    (SheafOfModules.overFunctor R W)) E ≫ c.hom
  have completed (k : ι) (hk : W ≤ U k)
      (K : CoherentModules W.toScheme)
      (lK : E.obj ((SheafOfModules.overMap R (homOfLE hk : W ⟶ U k)).obj (Li k)) ≅
        K.obj)
      (aK : K ⟶ Hw)
      (βK : (N.obj ⋙ SheafOfModules.overFunctor R W ⋙ E) ≅
        formalCompletionSystem (J.comap W.ι) K.obj)
      (hbK : E.map ((SheafOfModules.overMap R (homOfLE hk : W ⟶ U k)).map (bi k) ≫
          (SheafOfModules.overFunctorMap R (homOfLE hk : W ⟶ U k)).hom.app H.obj) =
        lK.hom ≫ aK.hom)
      (hqK : ∀ n : ℕᵒᵖ,
        E.map ((SheafOfModules.overMap R (homOfLE hk : W ⟶ U k)).map (qi k n) ≫
            (SheafOfModules.overFunctorMap R (homOfLE hk : W ⟶ U k)).hom.app
              (N.obj.obj n)) =
          lK.hom ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) K.obj ≫
            βK.inv.app n) :
      βK.hom ≫ formalCompletionMap (J.comap W.ι) aK.hom = d := by
    let T := SheafOfModules.overMap R (homOfLE hk : W ⟶ U k)
    generalize hη : SheafOfModules.overFunctorMap R (homOfLE hk : W ⟶ U k) = η
      at hbK hqK
    have component (n : ℕᵒᵖ) :
        formalModuleQuotientMap (J.comap W.ι) aK.hom (Nat.le_refl (n.unop + 1)) =
          βK.inv.app n ≫ d.app n := by
      have hp : Epi (formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) K.obj) := by
        dsimp [formalModuleQuotientπ]
        infer_instance
      apply (cancel_epi (formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) K.obj)).1
      apply (cancel_epi lK.hom).1
      have hloc := congrArg (fun t ↦ T.map t ≫ η.hom.app
        (formalModuleQuotient J (n.unop + 1) H.obj)) (hδ k n)
      simp only [Functor.map_comp, Category.assoc] at hloc
      have hnδ := η.hom.naturality (δ.hom.app n)
      change T.map ((δ.hom.app n).over (U k)) ≫
          η.hom.app (formalModuleQuotient J (n.unop + 1) H.obj) =
        η.hom.app (N.obj.obj n) ≫ (δ.hom.app n).over W at hnδ
      have hnπ := η.hom.naturality (formalModuleQuotientπ J (n.unop + 1) H.obj)
      change T.map ((formalModuleQuotientπ J (n.unop + 1) H.obj).over (U k)) ≫
          η.hom.app (formalModuleQuotient J (n.unop + 1) H.obj) =
        η.hom.app H.obj ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over W at hnπ
      rw [hnδ, hnπ] at hloc
      have he := congrArg (fun t ↦ E.map t ≫ c.hom.app n) hloc
      simp only [Functor.map_comp, Category.assoc] at he
      have hπ : formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) K.obj ≫
          formalModuleQuotientMap (J.comap W.ι) aK.hom (Nat.le_refl (n.unop + 1)) =
          aK.hom ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) Hw.obj :=
        cokernel.π_desc _ _ _
      have hbK' := hbK
      have hqK' := hqK n
      simp only [Functor.map_comp] at hbK' hqK'
      rw [← Category.assoc, ← Category.assoc, hqK',
        ← Category.assoc, ← Category.assoc, hbK', Category.assoc, hc n] at he
      rw [hπ]
      simpa only [d, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
        using he.symm
    apply NatTrans.ext
    funext n
    change βK.hom.app n ≫
      formalModuleQuotientMap (J.comap W.ι) aK.hom (Nat.le_refl (n.unop + 1)) = _
    rw [component n, Iso.hom_inv_id_app_assoc]
  have hdF := completed i hi F lF a βF hbF' hqF
  have hdG := completed j hj G lG a' βG hbG' hqG
  let θ : (completion W.toScheme (J.comap W.ι)).obj F ⟶
      (completion W.toScheme (J.comap W.ι)).obj G :=
    ObjectProperty.homMk (βF.inv ≫ βG.hom)
  have hθ : θ ≫ (completion W.toScheme (J.comap W.ι)).map a' =
      (completion W.toScheme (J.comap W.ι)).map a := by
    apply ObjectProperty.hom_ext
    change (βF.inv ≫ βG.hom) ≫ formalCompletionMap (J.comap W.ι) a'.hom =
      formalCompletionMap (J.comap W.ι) a.hom
    rw [Category.assoc, hdG, ← hdF]
    simp
  obtain ⟨g, hg, hgθ⟩ := torsionControlled_completion_hom_lift_exists
    (J.comap W.ι) Hw F G a a' ha ha' θ hθ
  let f : Ti.obj (Li i) ⟶ Tj.obj (Li j) :=
    E.preimage (lF.hom ≫ g.hom ≫ lG.inv)
  have hf : E.map f = lF.hom ≫ g.hom ≫ lG.inv := E.map_preimage _
  have hfb : f ≫ bwj = bwi := by
    apply E.map_injective
    rw [E.map_comp, hf, hbG', hbF']
    have hga : g.hom ≫ a'.hom = a.hom := congrArg (fun t ↦ t.hom) hg
    simp [Category.assoc, hga]
  have hfq (n : ℕᵒᵖ) : f ≫ qwj n = qwi n := by
    apply E.map_injective
    rw [E.map_comp, hf, hqG n, hqF n]
    have hgπ : g.hom ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) G.obj =
        formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) F.obj ≫
          (βF.inv.app n ≫ βG.hom.app n) := by
      have he := congrArg (fun t ↦ t.hom.app n) hgθ
      change formalModuleQuotientMap (J.comap W.ι) g.hom
        (Nat.le_refl (n.unop + 1)) = βF.inv.app n ≫ βG.hom.app n at he
      rw [← he]
      exact (cokernel.π_desc _ _ _).symm
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc g.hom, hgπ]
    simp
  refine ⟨f, ?_, ?_⟩
  · intro V hV
    have he := congrArg (fun t ↦ t.val.app (op (Over.mk (homOfLE hV)))) hfb
    change f.val.app (op (Over.mk (homOfLE hV))) ≫
      (bi j).val.app (op (Over.mk (homOfLE (hV.trans hj)))) =
        (bi i).val.app (op (Over.mk (homOfLE (hV.trans hi)))) at he
    exact he
  · intro n V hV
    have he := congrArg (fun t ↦ t.val.app (op (Over.mk (homOfLE hV)))) (hfq n)
    change f.val.app (op (Over.mk (homOfLE hV))) ≫
      (qi j n).val.app (op (Over.mk (homOfLE (hV.trans hj)))) =
        (qi i n).val.app (op (Over.mk (homOfLE (hV.trans hi)))) at he
    exact he

end AlgebraicGeometry
