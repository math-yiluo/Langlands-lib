/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
section
universe a av c cv d
variable {S : Type c} [Category.{cv} S] [Abelian S] [HasDerivedCategory.{d} S]
  {M : ℕ → Type a} [∀ n, Category.{av} (M n)] [∀ n, Abelian (M n)]
  [∀ n, HasDerivedCategory.{d} (M n)]
  {e : ∀ n, S ⥤ M n} [∀ n, (e n).Additive]
  {r : ∀ {m n : ℕ}, n ≤ m → M n ⥤ M m} [∀ m n (h : n ≤ m), (r h).Additive]
  {T : ∀ {m n : ℕ}, n ≤ m → M m ⥤ M n} [∀ m n (h : n ≤ m), (T h).Additive]
  {atensor : ∀ {m n : ℕ} (h : n ≤ m), T h ⊣ r h}
  {kflat : ∀ n, CochainComplex (M n) ℤ → Prop} {flat : ∀ n, M n → Prop}
  {norm : (∀ {m n : ℕ} (h : n ≤ m), e m ⟶ e n ⋙ r h) → Prop}
  {unitNorm : (∀ n, T (Nat.le_refl n) ≅ 𝟭 (M n)) → Prop}
  {assocNorm : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    T h₁ ⋙ T h₂ ≅ T (h₂.trans h₁)) → Prop}

-- Comparing the normalized derived adjunctions requires substantial instance synthesis.
private theorem below_mate
    (E : CoefficientEvaluationExtensionData e r T atensor kflat flat norm unitNorm assocNorm)
    {m n : ℕ} (h : m ≤ n) :
    ((mateEquiv (E.derivedAdj n) (E.scalar h).derivedAdj).symm
      (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫ E.transition h))) =
      (E.derivedBelow h).inv := by
  let := E.extensionAdditive
  let β := ((mateEquiv (E.derivedAdj n) (E.scalar h).derivedAdj).symm
    (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫ E.transition h)))
  have hb (P : CochainComplex (M n) ℤ) :
      β.app (DerivedCategory.Q.obj P) ≫
        (E.evaluation m).map ((E.counit n).app P) ≫
        (E.evaluationFactors m).hom.app
          (((E.extension n).mapHomologicalComplex (.up ℤ)).obj P) =
      (E.scalar h).counit.app P ≫ DerivedCategory.Q.map (E.belowComplex h P).inv := by
    have ht (K : CochainComplex S ℤ) :=
      E.transition_rep h K
    have hu (F : M n) :=
      E.hom_formula h F ((E.extension n).obj F) (𝟙 _)
    have hu' (F : M n) :
        (atensor h).homEquiv
          F _ ((E.below h).inv.app F) =
        (E.adj n).unit.app F ≫ (E.strictTransition h).app ((E.extension n).obj F) := by
      have hh := hu F
      erw [(e m).map_id, Category.comp_id, (E.adj n).homEquiv_id] at hh
      exact hh
    have hi (P : CochainComplex (M n) ℤ) :
        ((NatIso.mapHomologicalComplex (E.below h) (.up ℤ)).inv.app P) =
          (E.belowComplex h P).inv := by
      have he : (NatIso.mapHomologicalComplex (E.below h) (.up ℤ)).app P =
          E.belowComplex h P := by
        apply Iso.ext
        apply HomologicalComplex.hom_ext
        intro i
        exact (E.belowComplex_f h P i).symm
      exact congrArg Iso.inv he
    have hh := derivedMate_comparison
      ((E.adj n).mapHomologicalComplex (.up ℤ))
      ((atensor h).mapHomologicalComplex (.up ℤ))
      (E.derivedAdj n) (E.scalar h).derivedAdj
      (E.counit n) (E.scalar h).counit (E.evaluationFactors n)
      (E.scalar h).restrictionFactors (Iso.refl _) (E.evaluationFactors m)
      (E.transpose n) (E.scalar h).transpose
      (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫
        (E.strictTransition h).mapHomologicalComplex (.up ℤ)))
      (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫ E.transition h))
      (by
        intro K
        dsimp only [TwoSquare.mk, NatTrans.comp_app,
          Functor.comp_obj, Functor.id_obj, Functor.rightUnitor_hom_app, Functor.id_map,
          Iso.refl_hom, NatTrans.id_app]
        simpa only [Category.id_comp] using ht K)
      ((NatIso.mapHomologicalComplex (E.below h) (.up ℤ)).inv)
      (by
        intro P
        dsimp only [TwoSquare.mk, NatTrans.comp_app,
          Functor.rightUnitor_hom_app, Functor.id_map]
        erw [Category.id_comp]
        apply HomologicalComplex.hom_ext
        intro i
        exact hu' (P.X i)) P
    simpa only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Iso.refl_hom,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, hi] using hh
  let γ : (E.scalar h).derived ⟶ (E.scalar h).derived := β ≫ (E.derivedBelow h).hom
  have hγ : γ = 𝟙 _ := by
    let := (E.scalar h).isDerived
    apply Functor.leftDerived_ext _ (E.scalar h).counit
      (HomologicalComplex.quasiIso (M n) (.up ℤ))
    ext P
    change (β.app _ ≫ (E.derivedBelow h).hom.app _) ≫ _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
    have he := E.derivedBelow_rep h P
    have he' : (E.derivedBelow h).hom.app (DerivedCategory.Q.obj P) ≫
        (E.scalar h).counit.app P =
      (E.evaluation m).map ((E.counit n).app P) ≫
        (E.evaluationFactors m).hom.app
          (((E.extension n).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (E.belowComplex h P).hom := by
      rw [← he]
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [Category.assoc, he']
    have hb' := hb P
    simp only [← Category.assoc] at hb' ⊢
    rw [hb', Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  ext P
  apply (cancel_mono ((E.derivedBelow h).hom.app P)).1
  rw [Iso.inv_hom_id_app]
  exact NatTrans.congr_app hγ P

private theorem below_transpose
    (E : CoefficientEvaluationExtensionData e r T atensor kflat flat norm unitNorm assocNorm)
    {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (M n))
    (M : DerivedCategory S)
    (f : (E.derivedExtension n).obj P ⟶ M) :
    (E.scalar h).derivedAdj.homEquiv _ _
      ((E.derivedBelow h).inv.app P ≫ (E.evaluation m).map f) =
    (E.derivedAdj n).homEquiv _ _ f ≫ (E.transition h).app M := by
  rw [← below_mate E h]
  have ht := adjunctionMate_transpose (E.derivedAdj n) (E.scalar h).derivedAdj
    (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫ E.transition h)) P M f
  dsimp only [TwoSquare.mk, Functor.id_map, Functor.id_obj,
    NatTrans.comp_app, Functor.rightUnitor_hom_app] at ht
  exact ht.trans (congrArg
    (fun g ↦ (E.derivedAdj n).homEquiv P M f ≫ g)
    (Category.id_comp ((E.transition h).app M)))

end

section MateCalculus
universe a av b bv c cv d dv e ev f fv
variable {A : Type a} [Category.{av} A] {B₀ : Type b} [Category.{bv} B₀]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]

private theorem conjugate_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (P : A) (Q : B₀) (f : L.obj P ⟶ Q) :
    b.homEquiv P Q (e.hom.app P ≫ f) =
      a.homEquiv P Q f ≫ (conjugateIsoEquiv a b e).hom.app Q := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc]
  rw [show R.map f ≫ (conjugateIsoEquiv a b e).hom.app Q =
    (conjugateIsoEquiv a b e).hom.app (L.obj P) ≫ R'.map f from
      (conjugateIsoEquiv a b e).hom.naturality f]
  rw [← Category.assoc]
  erw [unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem conjugate_of_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (δ : R ≅ R')
    (h : ∀ P Q (f : L'.obj P ⟶ Q),
      b.homEquiv P Q f = a.homEquiv P Q (e.inv.app P ≫ f) ≫ δ.hom.app Q) :
    conjugateIsoEquiv a b e = δ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  have hh := h (R.obj Q) Q (e.hom.app _ ≫ a.counit.app Q)
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
  have hc := conjugate_transpose a b e (R.obj Q) Q (a.counit.app Q)
  have hi : a.homEquiv (R.obj Q) Q (a.counit.app Q) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id Q]
    exact Equiv.apply_symm_apply _ _
  rw [hi, Category.id_comp] at hh hc
  exact hc.symm.trans hh

private theorem conjugate_inverse_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (δ : R ≅ R') (P : A) :
    a.homEquiv P (L'.obj P)
        (((conjugateIsoEquiv a b).symm δ).inv.app P) ≫ δ.hom.app (L'.obj P) =
      b.unit.app P := by
  let i := (conjugateIsoEquiv a b).symm δ
  have hc : conjugateIsoEquiv a b i = δ := Equiv.apply_symm_apply _ _
  have ht := conjugate_transpose a b i P (L'.obj P) (i.inv.app P)
  rw [hc, Iso.hom_inv_id_app, Adjunction.homEquiv_id] at ht
  exact ht.symm

private theorem iso_inv_of_rep_comparison
    {V W X Y Z : A} (e : V ≅ W) (f : W ⟶ V) (u : V ⟶ X) [Mono u]
    (v : W ⟶ Y) (w : Y ⟶ Z) (r : X ⟶ Z) (s : Z ⟶ X)
    (hrs : r ≫ s = 𝟙 X) (hf : f ≫ u = v ≫ w ≫ s)
    (he : e.hom ≫ v ≫ w = u ≫ r) : f = e.inv := by
  apply (cancel_epi e.hom).1
  apply (cancel_mono u).1
  calc
    (e.hom ≫ f) ≫ u = (e.hom ≫ v ≫ w) ≫ s := by
      rw [Category.assoc, hf]
      simp only [Category.assoc]
    _ = (u ≫ r) ≫ s := congrArg (fun z ↦ z ≫ s) he
    _ = (e.hom ≫ e.inv) ≫ u := by
      rw [Category.assoc, hrs, Category.comp_id, e.hom_inv_id, Category.id_comp]

private theorem scalar_conjugate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (h : ∀ P Q (f : Fn.obj (TA.obj P) ⟶ Q),
      a.homEquiv P _ (an.homEquiv _ Q f) =
        am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q) :
    conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ := by
  apply conjugate_of_transpose
  intro P Q f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv P _ (an.homEquiv _ Q f) =
    am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q
  exact h P Q f

private theorem mate_of_unit
    {L : A ⥤ B₀} {R : B₀ ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {F : A ⥤ C} {G : B₀ ⥤ D}
    (α : F ⋙ L' ⟶ L ⋙ G) (β : R ⋙ F ⟶ G ⋙ R')
    (h : ∀ P, b.homEquiv _ _ (α.app P) =
      F.map (a.unit.app P) ≫ β.app (L.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ α)) = β := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext P
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ (α.app P) = b.homEquiv _ _
    ((((mateEquiv a b).symm (.mk _ _ _ _ β))).app P)
  exact (h P).trans (unit_mateEquiv_symm a b (.mk _ _ _ _ β) P)

private theorem scalar_inverse_mate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (β : RA ⋙ Fm ≅ Fn ⋙ RB)
    (hc : conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ)
    (hβ : ∀ P, am.homEquiv _ _ (β.hom.app P) =
      RA.map (an.unit.app P) ≫ δ.inv.app (Fn.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ γ.inv)) = β.hom := by
  apply (mateEquiv an am).injective
  have hh := iterated_mateEquiv_conjugateEquiv a b am an
    (.mk _ _ _ _ γ.inv)
  have hi : conjugateEquiv (a.comp an) (am.comp b) γ.inv = δ.inv := by
    exact congrArg Iso.inv hc
  rw [hi] at hh
  exact hh.trans (mate_of_unit an am β.hom δ.inv hβ).symm

private theorem mate_unit_of_eq
    {L : A ⥤ B₀} {R : B₀ ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {F : A ⥤ C} {G : B₀ ⥤ D}
    (α : F ⋙ L' ⟶ L ⋙ G) (β : R ⋙ F ⟶ G ⋙ R')
    (h : mateEquiv a b (.mk _ _ _ _ α) = β) (P : A) :
    F.map (a.unit.app P) ≫ β.app (L.obj P) =
      b.unit.app (F.obj P) ≫ R'.map (α.app P) := by
  have hu := unit_mateEquiv a b (.mk _ _ _ _ α) P
  change F.map (a.unit.app P) ≫ (mateEquiv a b (.mk _ _ _ _ α)).app _ = _ at hu
  rw [h] at hu
  exact hu

-- Pasting the open and scalar mates only uses the following abstract adjunctions.
private theorem open_singleton_mate_pasting
    {E : Type e} [Category.{ev} E] {F₀ : Type f} [Category.{fv} F₀]
    {Ls : E ⥤ F₀} {Rs : F₀ ⥤ E} (asys : Ls ⊣ Rs)
    {Ln : A ⥤ B₀} {Rn : B₀ ⥤ A} (an : Ln ⊣ Rn)
    {Lm : C ⥤ D} {Rm : D ⥤ C} (am : Lm ⊣ Rm)
    {Tx : A ⥤ C} {Rx : C ⥤ A} (ax : Tx ⊣ Rx)
    {Tz : B₀ ⥤ D} {Rz : D ⥤ B₀} (az : Tz ⊣ Rz)
    {Exn : E ⥤ A} {Exm : E ⥤ C} {Ezn : F₀ ⥤ B₀} {Ezm : F₀ ⥤ D}
    (em : Ls ⋙ Ezm ≅ Exm ⋙ Lm)
    (rn : Rs ⋙ Exn ≅ Ezn ⋙ Rn) (rm : Rs ⋙ Exm ≅ Ezm ⋙ Rm)
    (τx : Exn ⟶ Exm ⋙ Rx) (τz : Ezn ⟶ Ezm ⋙ Rz)
    (γ : Tz ⋙ Rm ≅ Rn ⋙ Tx) (δ : Rz ⋙ Rn ≅ Rm ⋙ Rx)
    (hem : (mateEquiv asys am).symm (.mk _ _ _ _ rm.hom) = em.inv)
    (hs : mateEquiv az ax (.mk _ _ _ _ γ.inv) = δ.hom)
    (ht : ∀ N, τx.app (Rs.obj N) ≫ Rx.map (rm.hom.app N) =
      rn.hom.app N ≫ Rn.map (τz.app N) ≫ δ.hom.app (Ezm.obj N))
    (q : Tx ⋙ Lm ≅ Ln ⋙ Tz)
    (hq : mateEquiv an am (.mk _ _ _ _ q.hom) = γ.inv)
    (P : A) (K : E) (N : F₀) (f : Ls.obj K ⟶ N)
    (bx : Exm.obj K ≅ Tx.obj P) (bz : Ezm.obj N ≅ Tz.obj (Ln.obj P))
    (v : P ⟶ Exn.obj (Rs.obj N)) (z : Ln.obj P ⟶ Ezn.obj N)
    (hx : ax.homEquiv _ _ (bx.inv ≫ Exm.map (asys.homEquiv _ _ f)) =
      v ≫ τx.app (Rs.obj N))
    (hi : v ≫ rn.hom.app N = an.unit.app P ≫ Rn.map z)
    (hz : z ≫ τz.app N ≫ Rz.map bz.hom = az.unit.app (Ln.obj P)) :
    Ezm.map f ≫ bz.hom = em.hom.app K ≫ Lm.map bx.hom ≫ q.hom.app P := by
  apply (cancel_epi (em.inv.app K)).1
  apply (cancel_epi (Lm.map bx.inv)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  apply (am.homEquiv _ _).injective
  rw [am.homEquiv_naturality_right]
  simp only [Category.assoc]
  rw [am.homEquiv_naturality_left, ← hem, adjunctionMate_transpose]
  simp only [← Category.assoc]
  apply (ax.homEquiv _ _).injective
  rw [ax.homEquiv_naturality_right, ax.homEquiv_naturality_right, hx]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [ht]
  simp only [← Category.assoc]
  rw [hi]
  slice_lhs 4 5 => erw [← δ.hom.naturality]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  simp only [← Category.assoc] at hz
  rw [hz]
  have hqu := mate_unit_of_eq an am q.hom γ.inv hq P
  rw [am.homEquiv_unit, ← hqu, ax.homEquiv_naturality_left]
  have hsu := mate_unit_of_eq az ax γ.inv δ.hom hs (Ln.obj P)
  rw [ax.homEquiv_unit]
  simpa only [Functor.id_obj, Functor.comp_obj, Category.assoc] using
    congrArg (fun z ↦ an.unit.app P ≫ z) hsu

end MateCalculus

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

-- Compare representatives, then cancel using the abstract categorical identity.
private theorem open_evaluation_mate
    (S : StrictEtaleCompactSupport O t c) (n : ℕ) :
    ((mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm
      (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)) =
    (S.openDerivedEvaluation n).inv := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  have h := derivedMate_comparison
    (S.val.openAdjunction.mapHomologicalComplex (.up ℤ))
    ((S.val.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ))
    S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
    S.val.openFactors.hom (S.val.levelOpenFactors n).hom
    S.openDerived.system.inverseFactors (S.openDerived.level n).inverseFactors
    (S.PX.evaluationFactors n) (S.PZ.evaluationFactors n)
    S.property.2.2.1 (S.property.2.2.2.1 n)
    (.mk _ _ _ _
      ((S.openImage.inverseEvaluation n).hom.mapHomologicalComplex (.up ℤ)))
    (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)
    (S.openDerived.inverseEvaluation_rep n)
    ((S.val.openEvaluation n).inv.mapHomologicalComplex (.up ℤ))
    (by
      intro K
      ext1 i
      change (S.val.levelOpenAdjunction n).homEquiv _ _
        ((S.val.openEvaluation n).inv.app (K.X i)) = _
      have hh := unit_mateEquiv S.val.openAdjunction (S.val.levelOpenAdjunction n)
        (.mk _ _ _ _ (S.val.openEvaluation n).inv) (K.X i)
      change _ ≫ ((mateEquiv S.val.openAdjunction (S.val.levelOpenAdjunction n)
        (.mk _ _ _ _ (S.val.openEvaluation n).inv))).app _ = _ at hh
      rw [← S.property.2.1 n] at hh
      exact hh.symm) P
  refine iso_inv_of_rep_comparison
    ((S.openDerivedEvaluation n).app (DerivedCategory.Q.obj P)) _
    ((S.PZ.evaluation n).map (S.val.openFactors.hom.app P) ≫
      (S.PZ.evaluationFactors n).hom.app
        ((S.val.openExtension.mapHomologicalComplex (.up ℤ)).obj P))
    _ _ (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (S.val.openEvaluation n) (.up ℤ)).hom.app P))
    _ ?_ h ?_
  · exact (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (S.val.openEvaluation n) (.up ℤ)).app P)).hom_inv_id
  · rw [Category.assoc]
    exact S.property.2.2.2.2 n P

-- Perform the two Hom transposes in the abstract mate-pasting lemma.
/-- Explicit mate-pasting remainder for the open singleton evaluation.
Source: Zheng, Construction 5.14 and Lemma 5.16.
(blueprint: lem-pur-etale-brown-open-singleton-evaluation-core).
The defining conjugate expansion of the insertion is first reduced to this
explicit composite; the remaining equality is the scalar/open mate square. -/
theorem etaleBrownOpenSingletonEvaluationCore
    (S : StrictEtaleCompactSupport O t c) {m n : ℕ} (h : m ≤ n)
    (q : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
    (hq : (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ q.hom)) = (S.openDerived.derivedTensor h).inv)
    (P : DerivedCategory (strictEtaleLevel X O t n)) :
    (S.PZ.evaluation m).map
        ((S.derivedOpen.map ((S.PX.derivedExtension n).map
          ((S.levelDerivedOpenAdjunction n).unit.app P ≫
            (S.openDerived.level n).inverse.map
              ((S.PZ.derivedAdj n).unit.app ((S.levelDerivedOpen n).obj P)))) ≫
          S.derivedOpen.map ((S.PX.derivedExtension n).map
            ((S.openDerived.inverseEvaluation n).inv.app
              ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)))) ≫
          S.derivedOpen.map ((S.PX.derivedAdj n).counit.app
            (S.openDerived.system.inverse.obj
              ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)))) ≫
          S.derivedOpenAdjunction.counit.app
            ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)))) ≫
      (S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P) =
    (S.openDerivedEvaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
      (S.levelDerivedOpen m).map ((S.PX.derivedBelow h).hom.app P) ≫ q.hom.app P := by
  let i := ((conjugateIsoEquiv
    ((S.PX.derivedAdj n).comp S.derivedOpenAdjunction)
    ((S.levelDerivedOpenAdjunction n).comp (S.PZ.derivedAdj n))).symm
      (S.openDerived.inverseEvaluation n)).symm
  suffices H : (S.PZ.evaluation m).map (i.hom.app P) ≫
      (S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P) =
      (S.openDerivedEvaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
        (S.levelDerivedOpen m).map ((S.PX.derivedBelow h).hom.app P) ≫ q.hom.app P by
    simpa [i, mateEquiv, conjugateEquiv, Category.assoc] using H
  have hi : (S.PX.derivedAdj n).homEquiv _ _
      (S.derivedOpenAdjunction.homEquiv _ _ (i.hom.app P)) ≫
        (S.openDerived.inverseEvaluation n).hom.app
          ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)) =
      (S.levelDerivedOpenAdjunction n).unit.app P ≫
        (S.openDerived.level n).inverse.map
          ((S.PZ.derivedAdj n).unit.app ((S.levelDerivedOpen n).obj P)) := by
    have ht := conjugate_inverse_transpose
      ((S.PX.derivedAdj n).comp S.derivedOpenAdjunction)
      ((S.levelDerivedOpenAdjunction n).comp (S.PZ.derivedAdj n))
      (S.openDerived.inverseEvaluation n) P
    rw [Adjunction.comp_unit_app] at ht
    simp only [Adjunction.comp_homEquiv] at ht
    exact ht
  have hs : (mateEquiv (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
      (.mk _ _ _ _ (S.openDerived.derivedTensor h).inv)) =
        (S.openDerived.restrictedInverse h).hom := by
    exact scalar_inverse_mate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
      (S.openDerived.level n).adjunction (S.openDerived.level m).adjunction
      (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
      (S.openDerived.restrictedInverse h)
      (scalar_conjugate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
        (S.openDerived.level n).adjunction (S.openDerived.level m).adjunction
        (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
        (S.openDerived.restrictedDirect_mate h))
      (S.openDerived.restrictedInverse_mate h)
  have hz := below_transpose S.PZ h ((S.levelDerivedOpen n).obj P)
    ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)) (𝟙 _)
  erw [(S.PZ.evaluation m).map_id, Category.comp_id,
    (S.PZ.derivedAdj n).homEquiv_id] at hz
  have hz' : (S.PZ.derivedAdj n).unit.app ((S.levelDerivedOpen n).obj P) ≫
      (S.PZ.transition h).app
        ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)) ≫
      (S.PZ.scalar h).restriction.map
        ((S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P)) =
        (S.PZ.scalar h).derivedAdj.unit.app ((S.levelDerivedOpen n).obj P) := by
    erw [← Category.assoc, ← hz, Adjunction.homEquiv_unit,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  exact open_singleton_mate_pasting S.derivedOpenAdjunction
    (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
    (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
    (S.openDerivedEvaluation m) (S.openDerived.inverseEvaluation n)
    (S.openDerived.inverseEvaluation m) (S.PX.transition h) (S.PZ.transition h)
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedInverse h)
    (open_evaluation_mate O t c S m) hs (S.openDerived.inverseTransition h) q hq P
    ((S.PX.derivedExtension n).obj P)
    ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)) (i.hom.app P)
    ((S.PX.derivedBelow h).app P)
    ((S.PZ.derivedBelow h).app ((S.levelDerivedOpen n).obj P))
    _ ((S.PZ.derivedAdj n).unit.app ((S.levelDerivedOpen n).obj P))
    (below_transpose S.PX h P _ (S.derivedOpenAdjunction.homEquiv _ _ (i.hom.app P)))
    hi hz'

end AlgebraicGeometry
