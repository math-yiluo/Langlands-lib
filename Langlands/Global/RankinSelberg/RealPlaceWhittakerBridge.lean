import Langlands.Global.RankinSelberg.RealLocalTheoryReduction
import Langlands.Global.RankinSelberg.RealPlaceIsotypic
import Langlands.Global.RankinSelberg.RealPlaceWhittakerEquivariance
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction

/-!
# Reducing the real-place model bridge to coefficient regularity

Actual restrictions are in the specified real local coefficient model if each local
standard-module map gives a Whittaker intertwiner. Real-place isotypy proves this
algebraic implication. The proved character and compact equivariance reduce that
per-map premise to smoothness, polynomial growth and right-derivative compatibility
of individual global Whittaker restrictions. These analytic properties remain open.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global.HeckeFunctionalEquation

local instance bridgeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance bridgeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Per-map intertwiner premise.** Let `T` be an actual cuspidal realization of `GL_(r+1)`
over a number field `F`, `ψ` a unitary character of the adeles trivial on `F` whose component
at the real place `w` is `ψ_a`, `A` a `(𝔤, K)`-map at `w` from the `O(r+1)`-finite standard
module of a list `d` of real blocks into `T`, and `b` a finite adelic point. Then the
map `f ↦ (g ↦ W_(A f)(ι_w(g) b))` (global Whittaker functions for `ψ`) is a Whittaker
intertwiner for `ψ_a`, and the same map for `ψ⁻¹` is one for `ψ_(-a)`. -/
def RealPlaceWhittakerIntertwinerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ w.1 w.2 a →
  ∀ (d : List RealBlock)
    (A : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space),
    T.realization.IsRealPlaceMap w d A →
  ∀ b : FiniteAdelicGL F (r + 1),
    (∃ B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealWhittakerIntertwiner r d a B ∧
        ∀ f, B f = fun g => cuspWhittaker F T ψ.complex (A f)
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∧
    ∃ B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealWhittakerIntertwiner r d (-a) B ∧
        ∀ f, B f = fun g => cuspWhittaker F T ψ.complex⁻¹ (A f)
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)

/-- The bridge premise follows from the per-map intertwiner premise. -/
def RealPlaceWhittakerModelReductionStatement : Prop :=
  RealPlaceWhittakerIntertwinerStatement.{u} → RealPlaceWhittakerModelStatement.{u}

/-- The real-place functional equation follows from the two local functional equations,
the per-map intertwiner premise and the contragredient pair-factor premise. -/
def RealPlaceFunctionalEquationIntertwinerReductionStatement : Prop :=
  RealLocalUnequalJacquetStatement →
    RealLocalPositiveEqualJacquetStatement → RealPlaceWhittakerIntertwinerStatement.{u} →
    RealPlaceContragredientPairLStatement.{u} →
    RealPlaceFunctionalEquationStatement.{u}

section Restriction

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The restrictions `g ↦ W_x(ι_w(g) b)` of the vectors `x` of the sum of the images of the
`(𝔤, K)`-maps lie in the Whittaker model, if each such map gives a Whittaker intertwiner. -/
theorem restriction_mem_realWhittakerModel {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r) (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsReal})
    (b : FiniteAdelicGL F (r + 1)) (d : List RealBlock) (a : ℝˣ)
    (hB : ∀ A : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space,
      T.realization.IsRealPlaceMap w d A →
      ∃ B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
          (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
        IsRealWhittakerIntertwiner r d a B ∧
          ∀ f, B f = fun g => cuspWhittaker F T χ (A f)
            (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))
    {x : T.Space} (hx : x ∈ T.realization.realPlaceIsotypic w d) :
    (fun g => cuspWhittaker F T χ x
      (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∈
        realWhittakerModel r d a := by
  induction hx using Submodule.iSup_induction' with
  | mem A y hy =>
    obtain ⟨f, rfl⟩ := hy
    obtain ⟨B, hBi, hBf⟩ := hB A.1 A.2
    rw [← hBf f]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hBi ⟨f, rfl⟩)
  | zero =>
    have h0 : (fun g => cuspWhittaker F T χ (0 : T.Space)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) = 0 := by
      funext g
      have h := UnramifiedWhittaker.cuspWhittaker_smul F χ T 0 (0 : T.Space)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)
      rw [zero_smul, zero_mul] at h
      exact h
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have hadd : (fun g => cuspWhittaker F T χ (y + z)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
        (fun g => cuspWhittaker F T χ y
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) +
        (fun g => cuspWhittaker F T χ z
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
      funext g
      exact UnramifiedWhittaker.cuspWhittaker_add F χ hχ T y z _
    rw [hadd]
    exact Submodule.add_mem _ hy hz

end Restriction

theorem realPlaceWhittakerModelReduction :
    RealPlaceWhittakerModelReductionStatement.{u} := by
  intro hI F _ _ _ ψ hψ r T w a ha d hd W
  have hstd : IsStandardAdditiveCharacter F ψ.complex :=
    isStandardAdditiveCharacter_of_unitary ψ hψ
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ :=
    Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hstd
  have hall : ∀ x : T.Space, x ∈ T.realization.realPlaceIsotypic w d :=
    Submodule.eq_top_iff'.mp (T.realization.realPlaceIsotypic_eq_top T.irreducible hd)
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · obtain ⟨x, b, rfl⟩ := hW
    exact restriction_mem_realWhittakerModel T ψ.complex hstd w b d a
      (fun A hA => (hI F ψ hψ r T w a ha d A hA b).1) (hall x)
  · obtain ⟨x, b, rfl⟩ := hW
    exact restriction_mem_realWhittakerModel T ψ.complex⁻¹ hstd' w b d (-a)
      (fun A hA => (hI F ψ hψ r T w a ha d A hA b).2) (hall x)

theorem realPlaceFunctionalEquationIntertwinerReduction :
    RealPlaceFunctionalEquationIntertwinerReductionStatement.{u} :=
  fun hU hE hI hdual =>
    realPlaceLocalTheoryReduction hU hE (realPlaceWhittakerModelReduction hI) hdual

/-! ### The analytic premise -/

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- **Analytic premise.** Let `T` be an actual cuspidal realization of `GL_(r+1)` over a number
field `F`, `χ` a standard additive character of `𝔸_F`, `w` a real place, `b` a finite adelic
point and `x` a vector of `T`. Then the archimedean restriction
`W(g) = W_x(ι_w(g) b)` of the global Whittaker function of `x` for `χ` is smooth on
`GL_(r+1)(ℝ)`, has polynomial growth for Jacquet's height, and the restriction of the Lie
action at `w` of a real direction `X` on `x` is the right derivative of `W` along `X`. -/
def RealPlaceWhittakerAnalyticStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (χ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F χ →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsReal}) (b : FiniteAdelicGL F (r + 1)) (x : T.Space),
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
        (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ x
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∧
      (∃ (C : ℝ) (N : ℕ), ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
        ‖cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)‖ ≤
          C * realMatrixHeight g ^ N) ∧
      ∀ X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ,
        (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ
            (T.realization.realPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x)
            (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
          Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X
            (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ x
              (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))

/-- The per-map intertwiner premise follows from the analytic premise. -/
def RealPlaceWhittakerIntertwinerReductionStatement : Prop :=
  RealPlaceWhittakerAnalyticStatement.{u} → RealPlaceWhittakerIntertwinerStatement.{u}

/-- The real-place functional equation follows from the two local functional equations,
the analytic premise and the contragredient pair-factor premise. -/
def RealPlaceFunctionalEquationAnalyticReductionStatement : Prop :=
  RealLocalUnequalJacquetStatement →
    RealLocalPositiveEqualJacquetStatement → RealPlaceWhittakerAnalyticStatement.{u} →
    RealPlaceContragredientPairLStatement.{u} →
    RealPlaceFunctionalEquationStatement.{u}

section Analytic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator Classical in
/-- Under the analytic premise, the restriction map of a `(𝔤, K)`-map at `w`, for a standard
character `χ` with component `ψ_c` at `w`, is a Whittaker intertwiner for `c`. -/
theorem exists_restriction_isRealWhittakerIntertwiner
    (hAn : RealPlaceWhittakerAnalyticStatement.{u}) (χ : AddChar (Adeles F) ℂ)
    (hχstd : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsReal})
    (c : ℝˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((realScaledCharacter c
          (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ))
    {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r) (b : FiniteAdelicGL F (r + 1))
    {d : List RealBlock}
    {A : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space}
    (hA : T.realization.IsRealPlaceMap w d A) :
    ∃ B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealWhittakerIntertwiner r d c B ∧
        ∀ f, B f = fun g => cuspWhittaker F T χ (A f)
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) := by
  let B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ) :=
    { toFun := fun f g => cuspWhittaker F T χ (A f)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)
      map_add' := fun f f' => funext fun g =>
        (congrArg (fun y => cuspWhittaker F T χ y
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) (map_add A f f')).trans
          (UnramifiedWhittaker.cuspWhittaker_add F χ hχstd T _ _ _)
      map_smul' := fun z f => funext fun g =>
        (congrArg (fun y => cuspWhittaker F T χ y
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) (map_smul A z f)).trans
          (UnramifiedWhittaker.cuspWhittaker_smul F χ T z _ _) }
  refine ⟨B, ⟨fun f u hu g => ?_, fun f => ?_, fun f => ?_, fun k f f' hf' => ?_,
    fun X f f' hf' => ?_⟩, fun f => rfl⟩
  · exact realPlaceRestriction_mul_left χ hχstd w c hχ T b (A f) hu g
  · exact (hAn F χ hχstd r T w b (A f)).1
  · exact (hAn F χ hχstd r T w b (A f)).2.1
  · exact realPlaceRestriction_rightTranslation χ T w b hA k f f' hf'
  · exact Exists.elim (hA.2 X f) fun hfX he =>
      (congrArg (fun y => fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ y
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))
        ((congrArg A (Subtype.ext hf' : f' = ⟨_, hfX⟩)).trans he)).trans
        ((hAn F χ hχstd r T w b (A f)).2.2 X)

end Analytic

theorem realPlaceWhittakerIntertwinerReduction :
    RealPlaceWhittakerIntertwinerReductionStatement.{u} := by
  intro hAn F _ _ _ ψ hψ r T w a ha d A hA b
  have hstd : IsStandardAdditiveCharacter F ψ.complex :=
    isStandardAdditiveCharacter_of_unitary ψ hψ
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ :=
    Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hstd
  exact ⟨exists_restriction_isRealWhittakerIntertwiner hAn ψ.complex hstd w a
      (realComponent_complex ψ w a ha) T b hA,
    exists_restriction_isRealWhittakerIntertwiner hAn ψ.complex⁻¹ hstd' w (-a)
      (realComponent_complex_inv ψ w a ha) T b hA⟩

theorem realPlaceFunctionalEquationAnalyticReduction :
    RealPlaceFunctionalEquationAnalyticReductionStatement.{u} :=
  fun hU hE hAn hdual =>
    realPlaceFunctionalEquationIntertwinerReduction hU hE
      (realPlaceWhittakerIntertwinerReduction hAn) hdual

end Langlands.Global.RankinSelbergGlobal
