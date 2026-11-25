/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem epi_over {X : Scheme.{u}} {P Q : X.Modules}
    (q : P ⟶ Q) [Epi q] (U : X.Opens) : Epi (q.over U) := by
  let E := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U
  apply E.epi_of_epi_map
  have hn : E.map (q.over U) = e.hom.app P ≫
      (Scheme.Modules.restrictFunctor U.ι).map q ≫ e.inv.app Q := by
    apply (cancel_mono (e.hom.app Q)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact e.hom.naturality q
  rw [hn]
  infer_instance

private theorem restrict_quotient_iso_π {X : Scheme.{u}} (J : X.IdealSheafData)
    (P : X.Modules) [P.IsQuasicoherent] (U : X.Opens) (n : ℕ)
    {Q : U.toScheme.Modules} (e : (Scheme.Modules.restrictFunctor U.ι).obj P ≅ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (formalModuleQuotientπ J n P) ≫
      (restrictionQuotientIso J P U n).inv ≫
        formalModuleQuotientMap (J.comap U.ι) e.hom (Nat.le_refl n) =
          e.hom ≫ formalModuleQuotientπ (J.comap U.ι) n Q := by
  rw [← restrictionQuotientIso_π]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact quotientMap_π _ _ _

private theorem local_epi_cancel {X : Scheme.{u}} {P Q S : X.Modules}
    (q : P ⟶ Q) [Epi q] (A B W : X.Opens) (ha : W ≤ A) (hb : W ≤ B)
    (f : Q.over A ⟶ S.over A) (g : Q.over B ⟶ S.over B)
    (h : ∀ (V : X.Opens) (hVa : V ≤ A) (hVb : V ≤ B),
      (q.over A ≫ f).val.app (op (Over.mk (homOfLE hVa))) =
        (q.over B ≫ g).val.app (op (Over.mk (homOfLE hVb)))) :
    f.val.app (op (Over.mk (homOfLE ha))) =
      g.val.app (op (Over.mk (homOfLE hb))) := by
  let R := moduleRings X.toRingedSpace
  let TA := SheafOfModules.overMap R (homOfLE ha : W ⟶ A)
  let TB := SheafOfModules.overMap R (homOfLE hb : W ⟶ B)
  let ea := SheafOfModules.overFunctorMap R (homOfLE ha : W ⟶ A)
  let eb := SheafOfModules.overFunctorMap R (homOfLE hb : W ⟶ B)
  let f' : Q.over W ⟶ S.over W := (ea.app Q).inv ≫ TA.map f ≫ (ea.app S).hom
  let g' : Q.over W ⟶ S.over W := (eb.app Q).inv ≫ TB.map g ≫ (eb.app S).hom
  have he : f' = g' := by
    have := epi_over q W
    apply (cancel_epi (q.over W)).mp
    have hfa : q.over W ≫ f' = (ea.app P).inv ≫ TA.map (q.over A ≫ f) ≫
        (ea.app S).hom := by
      dsimp [f']
      rw [Functor.map_comp, ← Category.assoc]
      have hn := ea.inv.naturality q
      change q.over W ≫ (ea.app Q).inv =
        (ea.app P).inv ≫ TA.map (q.over A) at hn
      erw [hn, Category.assoc]
    have hgb : q.over W ≫ g' = (eb.app P).inv ≫ TB.map (q.over B ≫ g) ≫
        (eb.app S).hom := by
      dsimp [g']
      rw [Functor.map_comp, ← Category.assoc]
      have hn := eb.inv.naturality q
      change q.over W ≫ (eb.app Q).inv =
        (eb.app P).inv ≫ TB.map (q.over B) at hn
      erw [hn, Category.assoc]
    rw [hfa, hgb]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    change (q.over A ≫ f).val.app
        (op (Over.mk (homOfLE (V.unop.hom.le.trans ha)))) =
      (q.over B ≫ g).val.app (op (Over.mk (homOfLE (V.unop.hom.le.trans hb))))
    exact h V.unop.left _ _
  have hv := congrArg (fun t ↦ t.val.app (op (Over.mk (𝟙 W)))) he
  change f.val.app (op (Over.mk (homOfLE ha))) =
    g.val.app (op (Over.mk (homOfLE hb))) at hv
  exact hv

/-- Compatible local quotient maps identify a fixed coherent source's completion with N.
The source and arrow are supplied; this theorem only descends their quotient comparisons.

Source: Stacks Project, Tag 0889(1), compatibility after algebraic sheaf descent;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-compatible-quotient-formal-comparisons).

Proof: Restriction along an open immersion is exact and commutes with ideal-module
products and ideal powers. It therefore identifies each restricted quotient of F
with the quotient of Fi through ei, compatibly with the quotient projections.
Combining this normalized comparison with βi.inv gives an isomorphism from the
restricted quotient of F to N at each level. The normalization equation for pi
says that the projection followed by this isomorphism is pi. Quotient projections
are epimorphisms. Thus hcompat, checked at every open in a pairwise intersection,
identifies these isomorphisms there. Their inverses also agree there. The canonical
quotient transitions and the naturality of βi identify the component maps as an
isomorphism of inverse systems. Its inverse is ε. Precompose the required
factorization with the quotient projection; hδ gives equality, and cancellation
of this epimorphism proves the equation. For J=0 projections are isomorphisms;
for J=1 all quotients and N on the covering opens are zero; empty covers have
no comparison obligations.
-/
theorem compatible_quotient_formal_comparisons
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H) (a : F ⟶ H)
    (ι : Type u) (U : ι → X.Opens)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ei : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).obj F.obj ≅ (Fi i).obj)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (pi : ∀ (i : ι) (n : ℕᵒᵖ), F.obj.over (U i) ⟶ (N.obj.obj n).over (U i))
    (hpi : ∀ (i : ι) (n : ℕᵒᵖ),
      (Scheme.Modules.overEquiv (U i)).functor.map (pi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
      (Scheme.Modules.overFunctorEquiv (U i)).hom.app F.obj ≫ (ei i).hom ≫
        formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
          (βi i).inv.app n)
    (hcompat : ∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      (pi i n).val.app (op (Over.mk (homOfLE hi))) =
        (pi j n).val.app (op (Over.mk (homOfLE hj))))
    (hδ : ∀ (i : ι) (n : ℕᵒᵖ), pi i n ≫ (δ.hom.app n).over (U i) =
      a.hom.over (U i) ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)) :
    ∃ ε : ∀ i, N.obj ⋙ SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) (U i) ≅
        ((completion X J).obj F).obj ⋙ SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) (U i),
      (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        ((ε i).hom.app n).val.app (op (Over.mk (homOfLE hi))) =
          ((ε j).hom.app n).val.app (op (Over.mk (homOfLE hj)))) ∧
      (∀ (n : ℕᵒᵖ) (i : ι), (δ.hom.app n).over (U i) =
        (ε i).hom.app n ≫ (((completion X J).map a).hom.app n).over (U i)) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    have : F.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp
        F.property).1
    let c (i : ι) : formalCompletionSystem J F.obj ⋙
        Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι)
          ((Scheme.Modules.restrictFunctor (U i).ι).obj F.obj) :=
      (restrictionCompletionIso J F.obj (U i)).symm
    let m (i : ι) : formalCompletionSystem (J.comap (U i).ι)
        ((Scheme.Modules.restrictFunctor (U i).ι).obj F.obj) ≅
        formalCompletionSystem (J.comap (U i).ι) (Fi i).obj :=
      (formalCompletionFunctor (J.comap (U i).ι)).mapIso (ei i)
    let bsch (i : ι) : ((completion X J).obj F).obj ⋙
        Scheme.Modules.restrictFunctor (U i).ι ≅
        N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι :=
      c i ≪≫ m i ≪≫ (βi i).symm
    let R (i : ι) := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) (U i)
    let E (i : ι) := (Scheme.Modules.overEquiv (U i)).functor
    let T (i : ι) := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (E i)
    let d (i : ι) : (T i).obj (((completion X J).obj F).obj ⋙ R i) ≅
        (T i).obj (N.obj ⋙ R i) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv (U i)) ≪≫ bsch i ≪≫
          (Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv (U i))).symm ≪≫
            (Functor.associator _ _ _).symm
    let b (i : ι) : ((completion X J).obj F).obj ⋙ R i ≅ N.obj ⋙ R i :=
      (T i).preimageIso (d i)
    have hb (i : ι) (n : ℕᵒᵖ) :
        (formalModuleQuotientπ J (n.unop + 1) F.obj).over (U i) ≫ (b i).hom.app n =
          pi i n := by
      apply (E i).map_injective
      apply (cancel_mono ((Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n))).mp
      rw [hpi i n]
      simp only [Functor.map_comp]
      have hbm : (E i).map ((b i).hom.app n) =
          (Scheme.Modules.overFunctorEquiv (U i)).hom.app
            (((completion X J).obj F).obj.obj n) ≫ (bsch i).hom.app n ≫
              (Scheme.Modules.overFunctorEquiv (U i)).inv.app (N.obj.obj n) := by
        have hm : (T i).map ((b i).hom) = (d i).hom := (T i).map_preimage _
        have hm' := congrArg (fun f ↦ f.app n) hm
        change (E i).map ((b i).hom.app n) = (d i).hom.app n at hm'
        dsimp [d] at hm'
        exact hm'.trans (Category.id_comp _)
      rw [hbm]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      change (E i).map ((formalModuleQuotientπ J (n.unop + 1) F.obj).over (U i)) ≫
          (Scheme.Modules.overFunctorEquiv (U i)).hom.app
            (formalModuleQuotient J (n.unop + 1) F.obj) ≫ (bsch i).hom.app n = _
      have hn := (Scheme.Modules.overFunctorEquiv (U i)).hom.naturality
        (formalModuleQuotientπ J (n.unop + 1) F.obj)
      change (E i).map ((formalModuleQuotientπ J (n.unop + 1) F.obj).over (U i)) ≫
          (Scheme.Modules.overFunctorEquiv (U i)).hom.app
            (formalModuleQuotient J (n.unop + 1) F.obj) =
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app F.obj ≫
          (Scheme.Modules.restrictFunctor (U i).ι).map
            (formalModuleQuotientπ J (n.unop + 1) F.obj) at hn
      rw [← Category.assoc, hn, Category.assoc]
      congr 1
      change (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n.unop + 1) F.obj) ≫ (bsch i).hom.app n = _
      change (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n.unop + 1) F.obj) ≫
        (restrictionQuotientIso J F.obj (U i) (n.unop + 1)).inv ≫
          formalModuleQuotientMap (J.comap (U i).ι) (ei i).hom
            (Nat.le_refl (n.unop + 1)) ≫ (βi i).inv.app n = _
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (βi i).inv.app n)
          (restrict_quotient_iso_π J F.obj (U i) (n.unop + 1) (ei i)))
    refine ⟨fun i ↦ (b i).symm, ?_, ?_⟩
    · intro n i j W hi hj
      have : Epi (formalModuleQuotientπ J (n.unop + 1) F.obj) :=
        inferInstanceAs (Epi (cokernel.π
          (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι
            (n.unop + 1)).2 F.obj)))
      have he := local_epi_cancel (formalModuleQuotientπ J (n.unop + 1) F.obj)
        (U i) (U j) W hi hj ((b i).hom.app n) ((b j).hom.app n) (by
          intro V hVi hVj
          rw [hb i n, hb j n]
          exact hcompat n i j V hVi hVj)
      let ei := (SheafOfModules.evaluation ((moduleRings X.toRingedSpace).over (U i))
        (op (Over.mk (homOfLE hi)))).mapIso ((b i).app n)
      let ej := (SheafOfModules.evaluation ((moduleRings X.toRingedSpace).over (U j))
        (op (Over.mk (homOfLE hj)))).mapIso ((b j).app n)
      exact (Iso.inv_eq_inv ei ej).mpr he
    · intro n i
      apply (cancel_epi ((b i).hom.app n)).mp
      simp only [Iso.symm_hom, ← Category.assoc, (b i).hom_inv_id_app, Category.id_comp]
      have : Epi (formalModuleQuotientπ J (n.unop + 1) F.obj) :=
        inferInstanceAs (Epi (cokernel.π
          (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι
            (n.unop + 1)).2 F.obj)))
      have := epi_over (formalModuleQuotientπ J (n.unop + 1) F.obj) (U i)
      apply (cancel_epi ((formalModuleQuotientπ J (n.unop + 1) F.obj).over (U i))).mp
      rw [← Category.assoc, hb i n, hδ i n]
      change a.hom.over (U i) ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i) =
        (formalModuleQuotientπ J (n.unop + 1) F.obj).over (U i) ≫
          (formalModuleQuotientMap J a.hom (Nat.le_refl (n.unop + 1))).over (U i)
      simpa only [Functor.map_comp] using
        congrArg (fun f ↦ f.over (U i))
          (quotientMap_π J a.hom (Nat.le_refl (n.unop + 1))).symm
end AlgebraicGeometry
