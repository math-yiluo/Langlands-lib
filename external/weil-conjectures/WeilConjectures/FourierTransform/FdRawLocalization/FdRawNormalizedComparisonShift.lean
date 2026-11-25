/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Descent of the fixed integral scalar comparison

Source: trace-definition coefficient-category sentence, raw localization steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)


attribute [local irreducible] HasDerivedCategory.standard
  FdOrdinaryScalarTransport.complex FdOrdinaryScalarTransport.completion
  fdCoefficientTransportFactors pbcIntegralDatum completedAdicChangeData
  integralDetailedCoefficientComparison sfRationalTriangulationDatum
  sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.transition
  pbcScalarCommShift pbcRationalHasShift
  ScalarLocalization.composition ScalarLocalization.category

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  pbcFiniteField pbcFiniteFieldField pbcFiniteFieldAlgebra

/-- The integral-to-rational localization, viewed in the named coefficient stage. -/
def QS (E : Padic.FiniteCoefficientFields l Ω) :
    sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E :=
  sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T

/-- The localization shift comparison in the named coefficient stage. -/
private instance qsCommShift (E : Padic.FiniteCoefficientFields l Ω) :
    (QS l Ω T E).CommShift ℤ :=
  sfRationalLocalizationCommShift l (pbcFiniteField.{u} l Ω E) T

private theorem shiftOne_heq_of_eqToIso
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
    (Q : A ⥤ B) (Q' : A' ⥤ B') (S : B ⥤ B') (V : A ⥤ A')
    [Q.CommShift ℤ] [Q'.CommShift ℤ] [S.CommShift ℤ] [V.CommShift ℤ]
    (hF : Q ⋙ S = V ⋙ Q')
    (oQ : ∀ X, Q.obj ((shiftFunctor A (1 : ℤ)).obj X) = (shiftFunctor B (1 : ℤ)).obj (Q.obj X))
    (oQ' : ∀ X, Q'.obj ((shiftFunctor A' (1 : ℤ)).obj X) =
      (shiftFunctor B' (1 : ℤ)).obj (Q'.obj X))
    (hQ : ∀ X, (Q.commShiftIso (1 : ℤ)).hom.app X = eqToHom (oQ X))
    (hQ' : ∀ X, (Q'.commShiftIso (1 : ℤ)).hom.app X = eqToHom (oQ' X))
    [NatTrans.CommShift (eqToIso hF).hom ℤ] (X : A) :
    HEq ((S.commShiftIso (1 : ℤ)).hom.app (Q.obj X))
      (Q'.map ((V.commShiftIso (1 : ℤ)).hom.app X)) := by
  have hs := NatTrans.shift_app_comm (eqToIso hF).hom (1 : ℤ) X
  simp only [Functor.commShiftIso_comp_hom_app, eqToIso.hom, eqToHom_app, hQ, hQ',
    eqToHom_map] at hs
  exact ((comp_eqToHom_heq _ _).trans (eqToHom_comp_heq _ _)).symm.trans
    ((heq_of_eq hs).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)))

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem scalarFactors {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T ⋙
        sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E) T 0
          (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) =
      U l Ω T h ⋙ sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω L) T := by
  apply Functor.hext
    (fun K ↦ sfRationalScalarExtension_obj l (pbcFiniteField.{u} l Ω E) T 0
      (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) ⟨K⟩)
  intro K H f
  have h := sfRationalScalarExtension_map_tmul l (pbcFiniteField.{u} l Ω E) T 0
    (Fact.out : l.Prime).ne_zero (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) K H f 1
  simp only [map_one] at h
  dsimp only [AlgebraicallyClosedCoefficients.coefficientInclusion,
    AlgebraicallyClosedCoefficients.Coefficient,
    pbcFiniteField, pbcFiniteFieldField, pbcFiniteFieldAlgebra, pbcFiniteFieldInclusion,
    sfRationalConstructibleLocalization, ScalarLocalization.localization,
    Functor.comp_map, U] at *
  with_unfolding_all exact h

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- The framework transition is the localization of the integral transition. -/
theorem scalarFactors' {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    QS l Ω T E ⋙ scalar l Ω T h = U l Ω T h ⋙ QS l Ω T L := by
  unfold scalar GeneralAlgebraicallyClosedCoefficients.transition
  exact scalarFactors l Ω T h

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem qsLocalization (E : Padic.FiniteCoefficientFields l Ω) :
    (QS l Ω T E).IsLocalization
      (Rationalization.W
        (Submonoid.powers (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)))
        (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  have : ∀ n : ℤ,
      (shiftFunctor (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) n).Linear
        (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)) :=
    ScalarLocalization.semilinear_all_shift_linear _ _
  exact ScalarLocalization.semilinear_localization_isLocalization _ _ _

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem qsShiftOne (E : Padic.FiniteCoefficientFields l Ω)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    HEq (((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).commShiftIso
      (1 : ℤ)).hom.app X)
      (𝟙 ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj
        ((shiftFunctor _ (1 : ℤ)).obj X))) := by
  have := (sfRationalTriangulationDatum l (pbcFiniteField.{u} l Ω E)
    T).choose_spec.choose_spec.2.choose_spec.choose_spec.1 X
  exact this

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem qsShiftObj (E : Padic.FiniteCoefficientFields l Ω)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj
        ((shiftFunctor _ (1 : ℤ)).obj X) =
      (shiftFunctor _ (1 : ℤ)).obj
        ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj X) := by
  have := (sfRationalTriangulationDatum l (pbcFiniteField.{u} l Ω E)
    T).choose_spec.choose_spec.1
  exact (congrArg (fun F ↦ F.obj
    ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj X)) this).symm

private theorem eq_eqToHom_of_heq_id {C : Type*} [Category C] {A B : C} (e : A = B)
    (f : A ⟶ B) (h : HEq f (𝟙 A)) : f = eqToHom e := by
  subst e
  simpa using eq_of_heq h

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem qsShiftOne_eq (E : Padic.FiniteCoefficientFields l Ω)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).commShiftIso
      (1 : ℤ)).hom.app X = eqToHom (qsShiftObj l Ω T E X) :=
  eq_eqToHom_of_heq_id _ _ (qsShiftOne l Ω T E X)

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem qsObjShift (E : Padic.FiniteCoefficientFields l Ω)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (QS l Ω T E).obj ((shiftFunctor _ (1 : ℤ)).obj X) =
      (shiftFunctor (GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) (1 : ℤ)).obj
        ((QS l Ω T E).obj X) :=
  qsShiftObj l Ω T E X

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem qsCommShiftOne (E : Padic.FiniteCoefficientFields l Ω)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    ((QS l Ω T E).commShiftIso (1 : ℤ)).hom.app X = eqToHom (qsObjShift l Ω T E X) :=
  qsShiftOne_eq l Ω T E X

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem scalarShiftPred {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (q : (scalar l Ω T h).CommShift ℤ)
    (hq : letI := q; NatTrans.CommShift (eqToIso (scalarFactors' l Ω T h)).hom ℤ)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    letI := q
    HEq (((scalar l Ω T h).commShiftIso (1 : ℤ)).hom.app ((QS l Ω T E).obj X))
      ((QS l Ω T L).map (((U l Ω T h).commShiftIso (1 : ℤ)).hom.app X)) := by
  let := q
  have := hq
  exact shiftOne_heq_of_eqToIso (QS l Ω T E) (QS l Ω T L) (scalar l Ω T h) (U l Ω T h)
    (scalarFactors' l Ω T h) (qsObjShift l Ω T E) (qsObjShift l Ω T L)
    (qsCommShiftOne l Ω T E) (qsCommShiftOne l Ω T L) X


private theorem coefficient_congr_heq.{v, v'}
    {γ : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (_ : FiniteDimensional ℚ_[l] E), Sort v'}
    {β : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (dE : FiniteDimensional ℚ_[l] E)
      (L : Type u) [Field L] [Algebra ℚ_[l] L] (_ : FiniteDimensional ℚ_[l] L),
      (E →ₐ[ℚ_[l]] L) → γ E dE → Sort v}
    (F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (dE : FiniteDimensional ℚ_[l] E)
      (L : Type u) [Field L] [Algebra ℚ_[l] L] (dL : FiniteDimensional ℚ_[l] L)
      (ι : E →ₐ[ℚ_[l]] L) (X : γ E dE), β E dE L dL ι X)
    {E₁ E₂ L₁ L₂ : Type u} (fE₁ : Field E₁) (fE₂ : Field E₂) (aE₁ : Algebra ℚ_[l] E₁)
    (aE₂ : Algebra ℚ_[l] E₂) (dE₁ : FiniteDimensional ℚ_[l] E₁)
    (dE₂ : FiniteDimensional ℚ_[l] E₂)
    (fL₁ : Field L₁) (fL₂ : Field L₂) (aL₁ : Algebra ℚ_[l] L₁)
    (aL₂ : Algebra ℚ_[l] L₂) (dL₁ : FiniteDimensional ℚ_[l] L₁)
    (dL₂ : FiniteDimensional ℚ_[l] L₂) (ι₁ : E₁ →ₐ[ℚ_[l]] L₁) (ι₂ : E₂ →ₐ[ℚ_[l]] L₂)
    (X₁ : γ E₁ dE₁) (X₂ : γ E₂ dE₂)
    (hE : E₁ = E₂) (hfE : HEq fE₁ fE₂) (haE : HEq aE₁ aE₂)
    (hL : L₁ = L₂) (hfL : HEq fL₁ fL₂) (haL : HEq aL₁ aL₂) (hι : HEq ι₁ ι₂)
    (hX : HEq X₁ X₂) :
    HEq (F E₁ dE₁ L₁ dL₁ ι₁ X₁) (F E₂ dE₂ L₂ dL₂ ι₂ X₂) := by
  subst hE hL
  cases hfE
  cases haE
  cases hfL
  cases haL
  cases hι
  cases hX
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem uShift_heq {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (X : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    HEq ((QS l Ω T L).map (((U l Ω T h).commShiftIso (1 : ℤ)).hom.app X))
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) T).map
        (((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h).commShiftIso
          (1 : ℤ)).hom.app X)) := by
  unfold QS uCommShift GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift
  exact coefficient_congr_heq l (γ := fun E _ _ _ ↦ sfIntegralConstructibleCategory l E T)
    (fun E _ _ _ L _ _ _ ι X ↦ (sfRationalConstructibleLocalization l L T).map
      ((@Functor.commShiftIso _ _ _ _
        (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι T) _ _ _ _
        (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
          l E L ι T).exists.choose (1 : ℤ)).hom.app X))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem scalarShiftSquare {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    NatTrans.CommShift (eqToIso (scalarFactors' l Ω T h)).hom ℤ := by
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)))
    (sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
  have := qsLocalization l Ω T E
  let e := eqToIso (scalarFactors' l Ω T h)
  let : Localization.Lifting (QS l Ω T E) W (U l Ω T h ⋙ QS l Ω T L) (scalar l Ω T h) := ⟨e⟩
  obtain ⟨q, hq⟩ : ∃ q : (scalar l Ω T h).CommShift ℤ,
      letI := q; NatTrans.CommShift e.hom ℤ :=
    ⟨Functor.commShiftOfLocalization (QS l Ω T E) W ℤ (U l Ω T h ⋙ QS l Ω T L)
      (scalar l Ω T h),
    NatTrans.commShift_iso_hom_of_localization (QS l Ω T E) W ℤ (U l Ω T h ⋙ QS l Ω T L)
      (scalar l Ω T h)⟩
  have hqeq : q = scalarCommShift l Ω T h := by
    apply (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      l Ω T E L h).unique
    · intro K
      obtain ⟨X⟩ := K
      exact (scalarShiftPred l Ω T h q hq X).trans (uShift_heq l Ω T h X)
    · exact (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
        l Ω T E L h).exists.choose_spec
  exact hqeq ▸ hq


private theorem commShift_eqToIso
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) [sF : F.CommShift ℤ] [sG : G.CommShift ℤ] (h : F = G)
    (hs : ∀ (n : ℤ) K,
      HEq ((F.commShiftIso n).hom.app K) ((G.commShiftIso n).hom.app K)) :
    NatTrans.CommShift (eqToIso h).hom ℤ := by
  cases h
  have hi (n : ℤ) : Functor.commShiftIso F (self := sF) n =
      Functor.commShiftIso F (self := sG) n := by
    apply Iso.ext
    ext K
    exact eq_of_heq (hs n K)
  have he : sF = sG := by
    cases sF
    cases sG
    congr 1
    funext n
    exact hi n
  cases he
  change NatTrans.CommShift (𝟙 F) ℤ
  infer_instance

private theorem commShift_eq_of_heq {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, HEq (Functor.commShiftIso F (self := s) n)
      (Functor.commShiftIso F (self := t) n)) : s = t := by
  cases s
  cases t
  congr 1
  funext n
  exact eq_of_heq (h n)

private theorem stageFactors (E : Padic.FiniteCoefficientFields l Ω) :
    sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T ⋙
        suppliedJ l Ω T stage E =
      I l Ω T stage E ⋙ pbcStageLocalization l Ω T E := by
  apply Functor.hext (fun K ↦ (stage E).objects ⟨K⟩)
  intro K H f
  have h := (stage E).tensors K H 1 f
  simp only [fdRawTensor, map_one] at h
  dsimp only [suppliedJ, I, sfRationalConstructibleLocalization,
    pbcStageLocalization, ScalarLocalization.localization, Functor.comp_map] at *
  with_unfolding_all exact h

private theorem suppliedStageShift (E : Padic.FiniteCoefficientFields l Ω) :
    NatTrans.CommShift (eqToIso (stageFactors l Ω T stage E)).hom ℤ := by
  apply commShift_eqToIso
  intro n K
  simp only [Functor.commShiftIso_comp_hom_app]
  exact (stage E).shift_normalization n K

universe uB vB in
/-- Transport of a shift-compatible equality of composites along a presentation change of the
middle category. -/
private theorem copy_eqToIso_commShift
    {A C D : Type*} {B B' : Type uB} [Category A] [Category C] [Category D]
    [HasShift A ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (b : Category.{vB} B) (b' : Category.{vB} B') (s : @HasShift B ℤ b _)
    (s' : @HasShift B' ℤ b' _)
    (hB : B = B') (hb : HEq b b') (hs : HEq s s')
    (Q : @Functor A _ B b) (Q' : @Functor A _ B' b')
    (cQ : @Functor.CommShift A B _ b Q ℤ _ _ s) (cQ' : @Functor.CommShift A B' _ b' Q' ℤ _ _ s')
    (hQ : HEq Q Q') (hcQ : HEq cQ cQ')
    (J : @Functor B b D _) (J' : @Functor B' b' D _)
    (cJ : @Functor.CommShift B D b _ J ℤ _ s _) (cJ' : @Functor.CommShift B' D b' _ J' ℤ _ s' _)
    (hJ : HEq J J') (hcJ : ∀ n : ℤ, HEq (@Functor.commShiftIso B D b _ J ℤ _ s _ cJ n)
      (@Functor.commShiftIso B' D b' _ J' ℤ _ s' _ cJ' n))
    (I : A ⥤ C) (P : C ⥤ D) [I.CommShift ℤ] [P.CommShift ℤ]
    (h : @Functor.comp A _ B b D _ Q J = I ⋙ P)
    (h' : @Functor.comp A _ B' b' D _ Q' J' = I ⋙ P)
    (hc' : letI := b'; letI := s'; letI := cQ'; letI := cJ'
      NatTrans.CommShift (eqToIso h').hom ℤ) :
    letI := b; letI := s; letI := cQ; letI := cJ
    NatTrans.CommShift (eqToIso h).hom ℤ := by
  subst hB
  cases hb
  cases hs
  cases hQ
  cases hcQ
  cases hJ
  cases commShift_eq_of_heq J cJ cJ' hcJ
  exact hc'

/-- The supplied rational functor is the localization of the integral identity functor. -/
theorem stageFactorsJ (family : RationalFamily l Ω T stage)
    (E : Padic.FiniteCoefficientFields l Ω) :
    QS l Ω T E ⋙ J l Ω T stage family E = I l Ω T stage E ⋙ pbcStageLocalization l Ω T E := by
  have hJ : J l Ω T stage family E = suppliedJ l Ω T stage E := eq_of_heq (family.identity E)
  rw [hJ]
  exact stageFactors l Ω T stage E

private theorem coefficient_congr_heq₁.{v}
    {β : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (_ : FiniteDimensional ℚ_[l] E), Sort v}
    (F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (dE : FiniteDimensional ℚ_[l] E), β E dE)
    {E₁ E₂ : Type u} (fE₁ : Field E₁) (fE₂ : Field E₂) (aE₁ : Algebra ℚ_[l] E₁)
    (aE₂ : Algebra ℚ_[l] E₂) (dE₁ : FiniteDimensional ℚ_[l] E₁)
    (dE₂ : FiniteDimensional ℚ_[l] E₂)
    (hE : E₁ = E₂) (hfE : HEq fE₁ fE₂) (haE : HEq aE₁ aE₂) :
    HEq (F E₁ dE₁) (F E₂ dE₂) := by
  subst hE
  cases hfE
  cases haE
  rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationType (E : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E =
      sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T := rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationCategory (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
      (inferInstance :
        Category (sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  unfold GeneralAlgebraicallyClosedCoefficients.stageCategory
  exact coefficient_congr_heq₁ l (fun E _ _ _ ↦
    (inferInstance : Category (sfRationalConstructibleCategory l E T)))
    _ _ _ _ _ _ rfl HEq.rfl HEq.rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationPreadditive (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stagePreadditive l Ω T E)
      (inferInstance : Preadditive
        (sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  unfold GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  exact coefficient_congr_heq₁ l (fun E _ _ _ ↦
    (inferInstance : Preadditive (sfRationalConstructibleCategory l E T)))
    _ _ _ _ _ _ rfl HEq.rfl HEq.rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationShift (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageShift l Ω T E)
      (sfRationalConstructibleShift l (pbcFiniteField.{u} l Ω E) T) := by
  unfold GeneralAlgebraicallyClosedCoefficients.stageShift
  exact coefficient_congr_heq₁ l (fun E _ _ _ ↦ sfRationalConstructibleShift l E T)
    _ _ _ _ _ _ rfl HEq.rfl HEq.rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem presentationPretriangulated (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stagePretriangulated l Ω T E)
      (sfRationalConstructiblePretriangulated l (pbcFiniteField.{u} l Ω E) T) := by
  unfold GeneralAlgebraicallyClosedCoefficients.stagePretriangulated
  exact coefficient_congr_heq₁ l (fun E _ _ _ ↦ sfRationalConstructiblePretriangulated l E T)
    _ _ _ _ _ _ rfl HEq.rfl HEq.rfl

private theorem stageShiftSquare (family : RationalFamily l Ω T stage)
    (E : Padic.FiniteCoefficientFields l Ω) :
    NatTrans.CommShift (eqToIso (stageFactorsJ l Ω T stage family E)).hom ℤ := by
  have hQ : HEq (QS l Ω T E)
      (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T) := HEq.rfl
  have hcQ : HEq (qsCommShift l Ω T E)
      (sfRationalLocalizationCommShift l (pbcFiniteField.{u} l Ω E) T) := HEq.rfl
  exact copy_eqToIso_commShift _ _ _ _ (presentationType l Ω T E)
    (presentationCategory l Ω T E) (presentationShift l Ω T E) _ _ _ _ hQ hcQ _ _ _ _
    (family.identity E) (family.shift_identity E) (I l Ω T stage E)
    (pbcStageLocalization l Ω T E)
    (stageFactorsJ l Ω T stage family E) (stageFactors l Ω T stage E)
    (suppliedStageShift l Ω T stage E)

private theorem abstract_commShift
    {AE AL BE BL CE CL DE DL : Type*} [Category AE] [Category AL] [Category BE] [Category BL]
    [Category CE] [Category CL] [Category DE] [Category DL]
    [HasShift AE ℤ] [HasShift AL ℤ] [HasShift BE ℤ] [HasShift BL ℤ]
    [HasShift CE ℤ] [HasShift CL ℤ] [HasShift DE ℤ] [HasShift DL ℤ]
    (QE : AE ⥤ BE) (QL : AL ⥤ BL) (S : BE ⥤ BL) (V : AE ⥤ AL) (JE : BE ⥤ DE) (JL : BL ⥤ DL)
    (IE : AE ⥤ CE) (IL : AL ⥤ CL) (PE : CE ⥤ DE) (PL : CL ⥤ DL) (Cc : CE ⥤ CL) (PT : DE ⥤ DL)
    [QE.CommShift ℤ] [QL.CommShift ℤ] [S.CommShift ℤ] [V.CommShift ℤ] [JE.CommShift ℤ]
    [JL.CommShift ℤ] [IE.CommShift ℤ] [IL.CommShift ℤ] [PE.CommShift ℤ] [PL.CommShift ℤ]
    [Cc.CommShift ℤ] [PT.CommShift ℤ]
    (hS : QE ⋙ S = V ⋙ QL) [NatTrans.CommShift (eqToIso hS).hom ℤ]
    (hJE : QE ⋙ JE = IE ⋙ PE) [NatTrans.CommShift (eqToIso hJE).hom ℤ]
    (hJL : QL ⋙ JL = IL ⋙ PL) [NatTrans.CommShift (eqToIso hJL).hom ℤ]
    (b : IE ⋙ Cc ≅ V ⋙ IL) [NatTrans.CommShift b.inv ℤ]
    (c : PE ⋙ PT ≅ Cc ⋙ PL) [NatTrans.CommShift c.hom ℤ]
    (j : S ⋙ JL ≅ JE ⋙ PT)
    (hj : ∀ K, HEq (j.hom.app (QE.obj K)) (PL.map (b.inv.app K) ≫ c.inv.app (IE.obj K)))
    (hess : ∀ X : BE, ∃ Y : AE, X = QE.obj Y) :
    NatTrans.CommShift j.hom ℤ := by
  have key : Functor.whiskerLeft QE j.hom =
      (Functor.associator QE S JL).inv ≫ Functor.whiskerRight (eqToIso hS).hom JL ≫
        (Functor.associator V QL JL).hom ≫ Functor.whiskerLeft V (eqToIso hJL).hom ≫
        (Functor.associator V IL PL).inv ≫ Functor.whiskerRight b.inv PL ≫
        (Functor.associator IE Cc PL).hom ≫ Functor.whiskerLeft IE c.inv ≫
        (Functor.associator IE PE PT).inv ≫ Functor.whiskerRight (eqToIso hJE).inv PT ≫
        (Functor.associator QE JE PT).hom := by
    ext K
    apply eq_of_heq
    refine (hj K).trans ?_
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToIso.inv,
      eqToHom_app, eqToHom_map, Category.id_comp, Category.comp_id]
    rw [eqToHom_trans_assoc]
    exact (HEq.symm ((eqToHom_comp_heq _ _).trans
      (by rw [← Category.assoc]; exact comp_eqToHom_heq _ _)))
  have : NatTrans.CommShift (Functor.whiskerLeft QE j.hom) ℤ := by
    rw [key]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft j.hom QE (fun X ↦ by
    obtain ⟨Y, hY⟩ := hess X
    exact ⟨Y, eqToHom hY, inferInstance⟩)

private theorem jCommShift (family : RationalFamily l Ω T stage)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ)
    (j : RawComparison l Ω T stage family)
    (hcomponents : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K))))
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    NatTrans.CommShift (j h).hom ℤ := by
  have := scalarShiftSquare l Ω T h
  have := stageShiftSquare l Ω T stage family E
  have := stageShiftSquare l Ω T stage family L
  have := (hshift h).2
  have : NatTrans.CommShift (pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom ℤ := by
    have := (pbcScalarShift_exists l Ω T dT.out iT.out h).exists.choose_spec
    unfold pbcScalarCommShift
    exact this
  exact abstract_commShift (QS l Ω T E) (QS l Ω T L) (scalar l Ω T h) (U l Ω T h)
    (J l Ω T stage family E) (J l Ω T stage family L) (I l Ω T stage E) (I l Ω T stage L)
    (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T L) (C l Ω T h) ((P l Ω T).T h)
    (scalarFactors' l Ω T h) (stageFactorsJ l Ω T stage family E)
    (stageFactorsJ l Ω T stage family L) (b h)
    (pbcScalarIntegralComparison l Ω T dT.out iT.out h) (j h)
    (fun K ↦ hcomponents h K _ HEq.rfl)
    (fun X ↦ ⟨(X.obj : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T), rfl⟩)


universe uB vB in
/-- Transport of exactness along a presentation change of the source category. -/
private theorem copy_isTriangulated
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {B B' : Type uB} (b : Category.{vB} B) (b' : Category.{vB} B')
    (p : letI := b; Preadditive B) (p' : letI := b'; Preadditive B')
    (z : letI := b; HasZeroObject B) (z' : letI := b'; HasZeroObject B')
    (s : letI := b; HasShift B ℤ) (s' : letI := b'; HasShift B' ℤ)
    (a : letI := b; letI := p; letI := s; ∀ n : ℤ, (shiftFunctor B n).Additive)
    (a' : letI := b'; letI := p'; letI := s'; ∀ n : ℤ, (shiftFunctor B' n).Additive)
    (t : letI := b; letI := p; letI := z; letI := s; letI := a; Pretriangulated B)
    (t' : letI := b'; letI := p'; letI := z'; letI := s'; letI := a'; Pretriangulated B')
    (hB : B = B') (hb : HEq b b') (hp : HEq p p') (hs : HEq s s') (ht : HEq t t')
    (J : @Functor B b D _) (J' : @Functor B' b' D _)
    (cJ : letI := b; letI := s; J.CommShift ℤ) (cJ' : letI := b'; letI := s'; J'.CommShift ℤ)
    (hJ : HEq J J') (hcJ : ∀ n : ℤ, HEq (@Functor.commShiftIso B D b _ J ℤ _ s _ cJ n)
      (@Functor.commShiftIso B' D b' _ J' ℤ _ s' _ cJ' n))
    (hT : letI := b'; letI := p'; letI := z'; letI := s'; letI := a'; letI := t'; letI := cJ'
      J'.IsTriangulated) :
    letI := b; letI := p; letI := z; letI := s; letI := a; letI := t; letI := cJ
    J.IsTriangulated := by
  subst hB
  cases hb
  cases hp
  cases hs
  cases ht
  cases hJ
  cases commShift_eq_of_heq J cJ cJ' hcJ
  exact hT


private theorem jTriangulated (family : RationalFamily l Ω T stage)
    (E : Padic.FiniteCoefficientFields l Ω) : (J l Ω T stage family E).IsTriangulated :=
  copy_isTriangulated _ _ _ _ _ _ _ _ _ _ _ _ (presentationType l Ω T E)
    (presentationCategory l Ω T E) (presentationPreadditive l Ω T E) (presentationShift l Ω T E)
    (presentationPretriangulated l Ω T E) _ (suppliedJ l Ω T stage E) _ (stage E).shift
    (family.identity E) (family.shift_identity E) (stage E).exact


/-- A component-normalized raw comparison preserves the prescribed shifts and exactness.
Source: raw localization scalar-descent step 1, specified shift and exactness clause
(blueprint: lem-fd-raw-normalized-comparison-shift).

Proof: Precompose both endpoint functors with the integral localization. The stage
comparison's tensor formula identifies Q followed by J with I followed by the PBC
localization. Its shift_normalization identifies their shift data. The coefficient
owner's transition shift is normalized at degree one by the localized integral shift;
the zero and addition axioms extend this identification to every integer, including
negative integers by inversion. The PBC scalar comparison has its specified localized
shift. Thus the component formula identifies the prewhiskered comparison with the
composite of these shift-compatible identifications and the localization of b inverse.
The assumed shift square for b proves the square after precomposition; localization
is essentially surjective, so it proves the square on every rational object. The
inverse square follows by cancellation. Each J is the supplied exact stage comparison
with exactly its specified shift, by family.identity and family.shift_identity.
Both scalar transitions are exact with their prescribed shifts, so composition gives
the two endpoint exactness assertions. No faithful localization, proper inclusion,
nonzero object, or nonempty scheme is used. -/
theorem rawNormalizedComparisonShift
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ)
    (family : RationalFamily l Ω T stage)
    (j : RawComparison l Ω T stage family)
    (hcomponents : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K)))) :
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
        NatTrans.CommShift (j h).hom ℤ ∧ NatTrans.CommShift (j h).inv ℤ ∧
        (scalar l Ω T h ⋙ J l Ω T stage family L).IsTriangulated ∧
        (J l Ω T stage family E ⋙ (P l Ω T).T h).IsTriangulated) := by
  intro E L h
  have hj := jCommShift l Ω T stage family b hshift j hcomponents h
  have hJE := jTriangulated l Ω T stage family E
  have hJL := jTriangulated l Ω T stage family L
  exact ⟨hj, inferInstance, inferInstance, inferInstance⟩

end WeilConjectures.FdRawLocalization
