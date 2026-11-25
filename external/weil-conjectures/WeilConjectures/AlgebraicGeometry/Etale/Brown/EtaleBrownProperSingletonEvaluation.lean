/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Proper singleton evaluation

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16,
printed pp. 21 and 34--35; Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

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

private theorem scalar_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {CY : A ⥤ B} {RY : B ⥤ A} (ay : CY ⊣ RY)
    {CX : C ⥤ D} {RX : D ⥤ C} (ax : CX ⊣ RX)
    {Fn : A ⥤ C} {Rn : C ⥤ A} (an : Fn ⊣ Rn)
    {Fm : B ⥤ D} {Rm : D ⥤ B} (am : Fm ⊣ Rm)
    (γ : CY ⋙ Fm ≅ Fn ⋙ CX) (δ : RX ⋙ Rn ≅ Rm ⋙ RY)
    (hδ : ∀ (P : A) (Q : D) (f : Fm.obj (CY.obj P) ⟶ Q),
      ay.homEquiv P (Rm.obj Q) (am.homEquiv _ Q f) =
        an.homEquiv P (RX.obj Q)
          (ax.homEquiv (Fn.obj P) Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q)
    (q : CX ⋙ Rm ≅ Rn ⋙ CY)
    (hq : q.inv = (mateEquiv an am (.mk _ _ _ _ γ.hom))) (P : C) :
    ay.homEquiv _ _ (q.inv.app P) =
      Rn.map (ax.unit.app P) ≫ δ.hom.app (CX.obj P) := by
  have he := mateEquiv_counit an am (.mk _ _ _ _ γ.hom) P
  change Fm.map ((mateEquiv an am (.mk _ _ _ _ γ.hom)).app P) ≫
    am.counit.app (CX.obj P) = γ.hom.app (Rn.obj P) ≫ CX.map (an.counit.app P) at he
  rw [← hq] at he
  have hh := hδ (Rn.obj P) (CX.obj P)
    (γ.hom.app (Rn.obj P) ≫ CX.map (an.counit.app P))
  have hleft : am.homEquiv (CY.obj (Rn.obj P)) (CX.obj P)
      (γ.hom.app (Rn.obj P) ≫ CX.map (an.counit.app P)) = q.inv.app P := by
    rw [← he]
    exact (am.homEquiv _ _).apply_symm_apply (q.inv.app P)
  rw [hleft] at hh
  simp only [← Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.id_comp] at hh
  erw [ax.homEquiv_unit, ax.unit_naturality,
    an.homEquiv_naturality_right, ← an.homEquiv_symm_id,
    Equiv.apply_symm_apply, Category.id_comp] at hh
  exact hh

private theorem iterated_insertion_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {FY : A ⥤ C} {EY : C ⥤ A} (ay : FY ⊣ EY)
    {FZ : B ⥤ D} {EZ : D ⥤ B} (az : FZ ⊣ EZ)
    {Fn : A ⥤ B} {Rn : B ⥤ A} (an : Fn ⊣ Rn)
    {Fs : C ⥤ D} {Rs : D ⥤ C} (asys : Fs ⊣ Rs)
    (d : Rs ⋙ EY ≅ EZ ⋙ Rn) :
    let i := ((conjugateIsoEquiv (ay.comp asys) (an.comp az)).symm d).symm
    let a := (mateEquiv an asys (.mk _ _ _ _ i.hom))
    ∀ P, ay.homEquiv _ _ (a.app P) ≫ d.hom.app (FZ.obj P) =
      Rn.map (az.unit.app P) := by
  intro i a P
  have hh := iterated_mateEquiv_conjugateEquiv an asys ay az (.mk _ _ _ _ i.hom)
  have hc : conjugateEquiv (an.comp az) (ay.comp asys) i.hom = d.inv :=
    Equiv.apply_symm_apply _ _
  rw [hc] at hh
  have he : ((mateEquiv az ay).symm (.mk _ _ _ _ d.inv)) = a := by
    have hs : (mateEquiv az ay (.mk _ _ _ _ a)) = (.mk _ _ _ _ d.inv) := by
      refine NatTrans.ext (funext fun X ↦ ?_)
      exact congrArg (fun τ ↦ τ.app X) hh
    exact ((Equiv.symm_apply_eq _).2 hs.symm)
  have ht := adjunctionMate_transpose az ay (.mk _ _ _ _ d.inv) P (FZ.obj P) (𝟙 _)
  change ay.homEquiv _ _
    (((mateEquiv az ay).symm (.mk _ _ _ _ d.inv)).app P ≫ Rs.map (𝟙 _)) =
    Rn.map (az.homEquiv _ _ (𝟙 _)) ≫ d.inv.app (FZ.obj P) at ht
  rw [he] at ht
  erw [Rs.map_id, Category.comp_id, az.homEquiv_id] at ht
  erw [ht, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The evaluated proper singleton mate is the coefficient projection inverse.
Source: Zheng, Lemma 5.13, printed pp. 34--35, using the normalized transpose
of Construction 4.1
(blueprint: lem-pur-etale-brown-proper-singleton-evaluation).

Proof: transpose the asserted equality under the level-m proper inverse/direct
adjunction and then under the scalar extension/restriction adjunction. The equation
fixing q as the mate of derivedTensor rewrites the scalar part. The compatibility
of directEvaluation with geometric counits rewrites the geometric part. The
singleton below-level comparison is the scalar transpose of the derived transition:
verify this on flat-term K-flat representatives using derivedBelow_rep and the
ordinary singleton hom_formula, and descend by localization. The directTransition
identity now identifies the two resulting maps. Finally the defining conjugate
identity for insertion and the two triangle identities give the same singleton
adjunct on both sides. Injectivity of the two Hom transposes proves the equality.
No invertibility assertion for the singleton mate is used. In particular m=n is
covered by the normalized identity scalar extension, and zero coefficients require
no exceptional case. -/
theorem etaleBrownProperSingletonEvaluation
    (S : StrictEtaleCompactSupport O t c) {m n : ℕ} (h : m ≤ n)
    (q : (S.PZ.scalar h).derived ⋙ (S.properDerived.level m).direct ≅
      (S.properDerived.level n).direct ⋙ (S.PY.scalar h).derived)
    (hq : q.inv =
      (mateEquiv (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)))
    (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
    let insertion := ((conjugateIsoEquiv
      ((S.PY.derivedAdj n).comp S.properDerived.system.adjunction)
      (((S.properDerived.level n).adjunction).comp (S.PZ.derivedAdj n))).symm
        (S.properDerived.directEvaluation n)).symm
    let a := (mateEquiv (S.properDerived.level n).adjunction
      S.properDerived.system.adjunction (.mk _ _ _ _ insertion.hom))
    (S.PY.evaluation m).map (a.app P) ≫
      (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
      (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) =
    (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) ≫
      q.inv.app P := by
  intro insertion a
  have ha := iterated_insertion_mate (S.PY.derivedAdj n) (S.PZ.derivedAdj n)
    (S.properDerived.level n).adjunction S.properDerived.system.adjunction
    (S.properDerived.directEvaluation n) P
  change (S.PY.derivedAdj n).homEquiv _ _ (a.app P) ≫
    (S.properDerived.directEvaluation n).hom.app ((S.PZ.derivedExtension n).obj P) =
    (S.properDerived.level n).direct.map ((S.PZ.derivedAdj n).unit.app P) at ha
  have hz := below_transpose S.PZ h P ((S.PZ.derivedExtension n).obj P) (𝟙 _)
  erw [(S.PZ.evaluation m).map_id, Category.comp_id,
    (S.PZ.derivedAdj n).homEquiv_id] at hz
  have hz' : (S.PZ.derivedAdj n).unit.app P ≫
      (S.PZ.transition h).app ((S.PZ.derivedExtension n).obj P) ≫
      (S.PZ.scalar h).restriction.map ((S.PZ.derivedBelow h).hom.app P) =
      (S.PZ.scalar h).derivedAdj.unit.app P := by
    rw [← Category.assoc, ← hz, Adjunction.homEquiv_unit,
      Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  apply (cancel_epi ((S.PY.derivedBelow h).inv.app
    ((S.properDerived.level n).direct.obj P))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply ((S.PY.scalar h).derivedAdj.homEquiv _ _).injective
  rw [(S.PY.scalar h).derivedAdj.homEquiv_naturality_right,
    (S.PY.scalar h).derivedAdj.homEquiv_naturality_right,
    below_transpose S.PY h]
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    erw [S.properDerived.directTransition h ((S.PZ.derivedExtension n).obj P)]
  simp only [← Category.assoc]
  rw [ha]
  slice_lhs 3 4 =>
    erw [← (S.properDerived.restrictedDirect h).hom.naturality]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  simp only [← Category.assoc] at hz'
  rw [hz']
  exact (scalar_mate_unit (S.PY.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
    (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
    (S.properDerived.derivedTensor h) (S.properDerived.restrictedDirect h)
    (S.properDerived.restrictedDirect_mate h) q hq P).symm

end AlgebraicGeometry
