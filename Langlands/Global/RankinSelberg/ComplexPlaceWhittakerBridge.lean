import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Global.RankinSelberg.ComplexPlaceIsotypic
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerEquivariance
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction

/-!
# The bridge premise from an analytic premise

The bridge premise `ComplexPlaceWhittakerModelStatement` of the conditional reduction
`complexPlaceFunctionalEquationReduction` says that the archimedean restrictions
`g ↦ W_x(ι_w(g) b)` of global Whittaker functions of an actual cuspidal realization `T` lie in
the Whittaker model `complexWhittakerModel` of the parameter `d` of `T` at the complex place
`w`. This module reduces it first to `ComplexPlaceWhittakerIntertwinerStatement` (for every
`(𝔤, K)`-map `A` at `w` and finite adelic point `b`, the map `f ↦ (g ↦ W_(A f)(ι_w(g) b))` is a
Whittaker intertwiner), using `complexPlaceIsotypic_eq_top` and the linearity of `x ↦ W_x`, and
then to `ComplexPlaceWhittakerAnalyticStatement` (smoothness, polynomial growth and Lie
compatibility of `g ↦ W_x(ι_w(g) b)` for a single vector `x`), using the equivariance results of
`ComplexPlaceWhittakerEquivariance`. The premises are not proved here. See the paired Markdown.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator CategoryTheory.MonObj
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global.HeckeFunctionalEquation

private local instance bridgeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
private local instance bridgeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Per-map intertwiner premise.** Let `T` be an actual cuspidal realization of `GL_(r+1)`
over a number field `F`, `ψ` a unitary character of the adeles trivial on `F` whose component
at the complex place `w` is `ψ_a`, `A` a `(𝔤, K)`-map at `w` from the `U(r+1)`-finite standard
module of a list `d` of complex characters into `T`, and `b` a finite adelic point. Then the
map `f ↦ (g ↦ W_(A f)(ι_w(g) b))` (global Whittaker functions for `ψ`) is a Whittaker
intertwiner for `ψ_a`, and the same map for `ψ⁻¹` is one for `ψ_(-a)`. -/
def ComplexPlaceWhittakerIntertwinerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d : List ComplexCharacterData)
    (A : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space),
    T.realization.IsComplexPlaceMap w d A →
  ∀ b : FiniteAdelicGL F (r + 1),
    (∃ B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℂ → ℂ),
      IsComplexWhittakerIntertwiner r d a B ∧
        ∀ f, B f = fun g => cuspWhittaker F T ψ.complex (A f)
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∧
    ∃ B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℂ → ℂ),
      IsComplexWhittakerIntertwiner r d (-a) B ∧
        ∀ f, B f = fun g => cuspWhittaker F T ψ.complex⁻¹ (A f)
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)

/-- The bridge premise follows from the per-map intertwiner premise. -/
def ComplexPlaceWhittakerModelReductionStatement : Prop :=
  ComplexPlaceWhittakerIntertwinerStatement.{u} → ComplexPlaceWhittakerModelStatement.{u}

/-- The complex-place functional equation follows from the two local functional equations,
the per-map intertwiner premise, the minus-one and the contragredient premises. -/
def ComplexPlaceFunctionalEquationIntertwinerReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerIntertwinerStatement.{u} →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}

section Restriction

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The restrictions `g ↦ W_x(ι_w(g) b)` of the vectors `x` of the sum of the images of the
`(𝔤, K)`-maps lie in the Whittaker model, if each such map gives a Whittaker intertwiner. -/
theorem restriction_mem_complexWhittakerModel {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r) (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) (d : List ComplexCharacterData) (a : ℂˣ)
    (hB : ∀ A : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space,
      T.realization.IsComplexPlaceMap w d A →
      ∃ B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
          (Langlands.GeneralLinear (r + 1) ℂ → ℂ),
        IsComplexWhittakerIntertwiner r d a B ∧
          ∀ f, B f = fun g => cuspWhittaker F T χ (A f)
            (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))
    {x : T.Space} (hx : x ∈ T.realization.complexPlaceIsotypic w d) :
    (fun g => cuspWhittaker F T χ x
      (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∈
        complexWhittakerModel r d a := by
  induction hx using Submodule.iSup_induction' with
  | mem A y hy =>
    obtain ⟨f, rfl⟩ := hy
    obtain ⟨B, hBi, hBf⟩ := hB A.1 A.2
    rw [← hBf f]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hBi ⟨f, rfl⟩)
  | zero =>
    have h0 : (fun g => cuspWhittaker F T χ (0 : T.Space)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) = 0 := by
      funext g
      have h := UnramifiedWhittaker.cuspWhittaker_smul F χ T 0 (0 : T.Space)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)
      rw [zero_smul, zero_mul] at h
      exact h
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have hadd : (fun g => cuspWhittaker F T χ (y + z)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
        (fun g => cuspWhittaker F T χ y
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) +
        (fun g => cuspWhittaker F T χ z
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
      funext g
      exact UnramifiedWhittaker.cuspWhittaker_add F χ hχ T y z _
    rw [hadd]
    exact Submodule.add_mem _ hy hz

end Restriction

theorem complexPlaceWhittakerModelReduction :
    ComplexPlaceWhittakerModelReductionStatement.{u} := by
  intro hI F _ _ _ ψ hψ r T w a ha d hd W
  have hstd : IsStandardAdditiveCharacter F ψ.complex :=
    isStandardAdditiveCharacter_of_unitary ψ hψ
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ :=
    Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hstd
  have hall : ∀ x : T.Space, x ∈ T.realization.complexPlaceIsotypic w d :=
    Submodule.eq_top_iff'.mp (T.realization.complexPlaceIsotypic_eq_top T.irreducible hd)
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · obtain ⟨x, b, rfl⟩ := hW
    exact restriction_mem_complexWhittakerModel T ψ.complex hstd w b d a
      (fun A hA => (hI F ψ hψ r T w a ha d A hA b).1) (hall x)
  · obtain ⟨x, b, rfl⟩ := hW
    exact restriction_mem_complexWhittakerModel T ψ.complex⁻¹ hstd' w b d (-a)
      (fun A hA => (hI F ψ hψ r T w a ha d A hA b).2) (hall x)

theorem complexPlaceFunctionalEquationIntertwinerReduction :
    ComplexPlaceFunctionalEquationIntertwinerReductionStatement.{u} :=
  fun hU hE hI hsign hdual =>
    complexPlaceFunctionalEquationReduction hU hE (complexPlaceWhittakerModelReduction hI)
      hsign hdual

/-! ### The analytic premise -/

/-- **Analytic premise.** Let `T` be an actual cuspidal realization of `GL_(r+1)` over a number
field `F`, `χ` a standard additive character of `𝔸_F`, `w` a complex place, `b` a finite adelic
point and `x` a vector of `T`. Then the archimedean restriction
`W(g) = W_x(ι_w(g) b)` of the global Whittaker function of `x` for `χ` is smooth on
`GL_(r+1)(ℂ)`, has polynomial growth for Jacquet's height, and the restriction of the Lie
action at `w` of a real direction `X` on `x` is the right derivative of `W` along `X`. -/
def ComplexPlaceWhittakerAnalyticStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (χ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F χ →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (b : FiniteAdelicGL F (r + 1)) (x : T.Space),
    ContMDiff (Archimedean.matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞
        (fun g : Langlands.GeneralLinear (r + 1) ℂ => cuspWhittaker F T χ x
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∧
      (∃ (C : ℝ) (N : ℕ), ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
        ‖cuspWhittaker F T χ x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)‖ ≤
          C * complexMatrixHeight g ^ N) ∧
      ∀ X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
        (fun g : Langlands.GeneralLinear (r + 1) ℂ => cuspWhittaker F T χ
            (T.realization.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x)
            (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
          Archimedean.rightDerivative (Archimedean.matrixModel ℂ (r + 1)) X
            (fun g : Langlands.GeneralLinear (r + 1) ℂ => cuspWhittaker F T χ x
              (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))

/-- The per-map intertwiner premise follows from the analytic premise. -/
def ComplexPlaceWhittakerIntertwinerReductionStatement : Prop :=
  ComplexPlaceWhittakerAnalyticStatement.{u} → ComplexPlaceWhittakerIntertwinerStatement.{u}

/-- The complex-place functional equation follows from the two local functional equations,
the analytic premise, the minus-one and the contragredient premises. -/
def ComplexPlaceFunctionalEquationAnalyticReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerAnalyticStatement.{u} →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}

section Analytic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

open scoped Classical in
/-- Under the analytic premise, the restriction map of a `(𝔤, K)`-map at `w`, for a standard
character `χ` with component `ψ_c` at `w`, is a Whittaker intertwiner for `c`. -/
theorem exists_restriction_isComplexWhittakerIntertwiner
    (hAn : ComplexPlaceWhittakerAnalyticStatement.{u}) (χ : AddChar (Adeles F) ℂ)
    (hχstd : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (c : ℂˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((complexScaledCharacter c
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ))
    {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r) (b : FiniteAdelicGL F (r + 1))
    {d : List ComplexCharacterData}
    {A : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space}
    (hA : T.realization.IsComplexPlaceMap w d A) :
    ∃ B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℂ → ℂ),
      IsComplexWhittakerIntertwiner r d c B ∧
        ∀ f, B f = fun g => cuspWhittaker F T χ (A f)
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) := by
  let B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
    { toFun := fun f g => cuspWhittaker F T χ (A f)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)
      map_add' := fun f f' => funext fun g =>
        (congrArg (fun y => cuspWhittaker F T χ y
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) (map_add A f f')).trans
          (UnramifiedWhittaker.cuspWhittaker_add F χ hχstd T _ _ _)
      map_smul' := fun z f => funext fun g =>
        (congrArg (fun y => cuspWhittaker F T χ y
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) (map_smul A z f)).trans
          (UnramifiedWhittaker.cuspWhittaker_smul F χ T z _ _) }
  refine ⟨B, ⟨fun f u hu g => ?_, fun f => ?_, fun f => ?_, fun k f f' hf' => ?_,
    fun X f f' hf' => ?_⟩, fun f => rfl⟩
  · exact complexPlaceRestriction_mul_left χ hχstd w c hχ T b (A f) hu g
  · exact (hAn F χ hχstd r T w b (A f)).1
  · exact (hAn F χ hχstd r T w b (A f)).2.1
  · exact complexPlaceRestriction_rightTranslation χ T w b hA k f f' hf'
  · exact Exists.elim (hA.2 X f) fun hfX he =>
      (congrArg (fun y => fun g : Langlands.GeneralLinear (r + 1) ℂ => cuspWhittaker F T χ y
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))
        ((congrArg A (Subtype.ext hf' : f' = ⟨_, hfX⟩)).trans he)).trans
        ((hAn F χ hχstd r T w b (A f)).2.2 X)

end Analytic

theorem complexPlaceWhittakerIntertwinerReduction :
    ComplexPlaceWhittakerIntertwinerReductionStatement.{u} := by
  intro hAn F _ _ _ ψ hψ r T w a ha d A hA b
  have hstd : IsStandardAdditiveCharacter F ψ.complex :=
    isStandardAdditiveCharacter_of_unitary ψ hψ
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ :=
    Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hstd
  exact ⟨exists_restriction_isComplexWhittakerIntertwiner hAn ψ.complex hstd w a
      (complexComponent_complex ψ w a ha) T b hA,
    exists_restriction_isComplexWhittakerIntertwiner hAn ψ.complex⁻¹ hstd' w (-a)
      (complexComponent_complex_inv ψ w a ha) T b hA⟩

theorem complexPlaceFunctionalEquationAnalyticReduction :
    ComplexPlaceFunctionalEquationAnalyticReductionStatement.{u} :=
  fun hU hE hAn hsign hdual =>
    complexPlaceFunctionalEquationIntertwinerReduction hU hE
      (complexPlaceWhittakerIntertwinerReduction hAn) hsign hdual

end Langlands.Global.RankinSelbergGlobal
