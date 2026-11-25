/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.TorsionControlledOverlapCocycle
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Local algebraizations give an algebraic cocycle preserving the arrows and quotient maps.

Source: Stacks Project, Tag 0889(1), first sentence and uniqueness verification;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-local-cocycle).

Proof: Transfer each supplied Fi to Li on the over-site by the inverse of overEquiv;
li is its counit. Transfer ai through hHlocal to obtain bi. Define qi by transferring
quotientπ followed by βi.inv. Normalization hγ and hfactor give qi followed by δ equal
to bi followed by the quotient projection of H. On pairwise intersections restriction
preserves coherence, kernels, cokernels and their ideal-power annihilation bounds.
Normalized completion comparisons identify the two completions with N. Lift this
comparison and its inverse using torsion-controlled hom lifting. Completion
extensionality with the map to H makes the lifts inverse. The same extensionality
identifies composites on triple intersections, proving the cocycle. Transfer these
isomorphisms back to the over-site as θ. Their compatibility with bi is the lifting
factorization equation, and compatibility with qi is the equality of their completions
precomposed with quotient projections. Zero ideals give the original comparisons;
unit ideals force the bounded arrows to be isomorphisms; empty covers require no data.
-/
theorem torsionControlled_local_cocycle
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (γ : ∀ i, ((completion X J).obj H).obj ⋙
      Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) (Hlocal i).obj)
    (hγ : ∀ (i : ι) (n : ℕ),
      (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n + 1) H.obj) ≫ (γ i).hom.app (op n) =
        eqToHom (hHlocal i).symm ≫
          formalModuleQuotientπ (J.comap (U i).ι) (n + 1) (Hlocal i).obj)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ai : ∀ i, Fi i ⟶ Hlocal i)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (hfactor : ∀ i,
      Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor (U i).ι) ≫ (γ i).hom =
        (βi i).hom ≫ formalCompletionMap (J.comap (U i).ι) (ai i).hom)
    (hbound : ∀ i, ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel (ai i).hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel (ai i).hom))) :
    ∃ (Li : ∀ i, SheafOfModules ((moduleRings X.toRingedSpace).over (U i)))
    (li : ∀ i, (Scheme.Modules.overEquiv (U i)).functor.obj (Li i) ≅ (Fi i).obj)
    (bi : ∀ i, Li i ⟶ H.obj.over (U i))
    (qi : ∀ (i : ι) (n : ℕᵒᵖ), Li i ⟶ (N.obj.obj n).over (U i))
    (θ : ∀ i j,
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Li i) ≅
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Li j)),
      (∀ i, (Scheme.Modules.overEquiv (U i)).functor.map (bi i) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj ≫
          eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom) ∧
      (∀ (i : ι) (n : ℕᵒᵖ), (Scheme.Modules.overEquiv (U i)).functor.map (qi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
          (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
            (βi i).inv.app n) ∧
      (∀ (i : ι) (n : ℕᵒᵖ), qi i n ≫ (δ.hom.app n).over (U i) =
        bi i ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)) ∧
      (∀ (i j k : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (θ i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (θ j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) ∧
      (∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (bi j).val.app (op (Over.mk (homOfLE hj))) =
            (bi i).val.app (op (Over.mk (homOfLE hi)))) ∧
      (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE hj))) =
            (qi i n).val.app (op (Over.mk (homOfLE hi)))) := by
  classical
  let E (i : ι) := (Scheme.Modules.overEquiv (U i)).functor
  let Li (i : ι) := (Scheme.Modules.overEquiv (U i)).inverse.obj (Fi i).obj
  let li (i : ι) : (E i).obj (Li i) ≅ (Fi i).obj :=
    (Scheme.Modules.overEquiv (U i)).counitIso.app (Fi i).obj
  let c (i : ι) := Scheme.Modules.overFunctorEquiv (U i)
  let bi (i : ι) : Li i ⟶ H.obj.over (U i) :=
    (E i).preimage ((li i).hom ≫ (ai i).hom ≫ eqToHom (hHlocal i) ≫ (c i).inv.app H.obj)
  let qi (i : ι) (n : ℕᵒᵖ) : Li i ⟶ (N.obj.obj n).over (U i) :=
    (E i).preimage ((li i).hom ≫
      formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
        (βi i).inv.app n ≫ (c i).inv.app (N.obj.obj n))
  have hbi (i : ι) : (E i).map (bi i) ≫ (c i).hom.app H.obj ≫
      eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom := by
    simp [bi, Category.assoc]
  have hqi (i : ι) (n : ℕᵒᵖ) : (E i).map (qi i n) ≫ (c i).hom.app (N.obj.obj n) =
      (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
        (βi i).inv.app n := by
    simp [qi, Category.assoc]
  have hδ (i : ι) (n : ℕᵒᵖ) : qi i n ≫ (δ.hom.app n).over (U i) =
      bi i ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i) := by
    apply (E i).map_injective
    apply (cancel_mono ((c i).hom.app (((completion X J).obj H).obj.obj n))).mp
    apply (cancel_mono ((γ i).hom.app n)).mp
    simp only [Functor.map_comp, Category.assoc]
    have hnδ := (c i).hom.naturality (δ.hom.app n)
    have hnπ := (c i).hom.naturality (formalModuleQuotientπ J (n.unop + 1) H.obj)
    change (E i).map ((δ.hom.app n).over (U i)) ≫
        (c i).hom.app (((completion X J).obj H).obj.obj n) =
      (c i).hom.app (N.obj.obj n) ≫
        (Scheme.Modules.restrictFunctor (U i).ι).map (δ.hom.app n) at hnδ
    change (E i).map ((formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)) ≫
        (c i).hom.app (formalModuleQuotient J (n.unop + 1) H.obj) =
      (c i).hom.app H.obj ≫ (Scheme.Modules.restrictFunctor (U i).ι).map
        (formalModuleQuotientπ J (n.unop + 1) H.obj) at hnπ
    rw [← Category.assoc _ _ ((γ i).hom.app n), hnδ]
    simp only [Category.assoc]
    rw [← Category.assoc _ _ ((Scheme.Modules.restrictFunctor (U i).ι).map
      (δ.hom.app n) ≫ (γ i).hom.app n), hqi]
    have hfac : (Scheme.Modules.restrictFunctor (U i).ι).map (δ.hom.app n) ≫
        (γ i).hom.app n = (βi i).hom.app n ≫
          (formalCompletionMap (J.comap (U i).ι) (ai i).hom).app n :=
      congrArg (fun f ↦ f.app n) (hfactor i)
    rw [Category.assoc, hfac]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    change (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι)
        (n.unop + 1) (Fi i).obj ≫
          (formalCompletionMap (J.comap (U i).ι) (ai i).hom).app n =
      (E i).map (bi i) ≫
        (E i).map ((formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)) ≫
          (c i).hom.app (formalModuleQuotient J (n.unop + 1) H.obj) ≫ (γ i).hom.app n
    rw [← Category.assoc _ _ ((γ i).hom.app n), hnπ]
    simp only [Category.assoc]
    have hγn : (Scheme.Modules.restrictFunctor (U i).ι).map
        (formalModuleQuotientπ J (n.unop + 1) H.obj) ≫ (γ i).hom.app n =
      eqToHom (hHlocal i).symm ≫
        formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Hlocal i).obj :=
      hγ i n.unop
    rw [hγn]
    rw [← Category.assoc ((c i).hom.app H.obj) (eqToHom (hHlocal i).symm)
      (formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Hlocal i).obj)]
    erw [← Category.assoc ((E i).map (bi i))
      ((c i).hom.app H.obj ≫ eqToHom (hHlocal i).symm)
        (formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Hlocal i).obj), hbi i]
    have hπ : formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
        (formalCompletionMap (J.comap (U i).ι) (ai i).hom).app n =
      (ai i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι)
        (n.unop + 1) (Hlocal i).obj := cokernel.π_desc _ _ _
    rw [hπ, Category.assoc]
  obtain ⟨θ, hcoc, hbcompat, hqcompat⟩ := torsionControlled_overlap_cocycle
    J H N δ ι U Hlocal hHlocal Fi ai βi hbound
      Li li bi qi hbi hqi hδ
  exact ⟨Li, li, bi, qi, θ, hbi, hqi, hδ, hcoc, hbcompat, hqcompat⟩

end AlgebraicGeometry
