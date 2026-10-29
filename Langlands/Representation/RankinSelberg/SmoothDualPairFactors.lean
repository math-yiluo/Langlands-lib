import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.PadicPairFactors

/-!
# Actual smooth-dual pair factors

Bundle the published Gelfand–Kazhdan realization for the equivalence transport
APIs. Construct the actual smooth-dual L-factor from the explicit dual-pair
polynomial existence hypothesis.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField

section Equivalence

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- Choose an actual representation equivalence from the published theorem.
Its source is the inverse-transpose pullback and its target is the smooth dual. -/
def inverseTransposeSmoothDualEquiv
    (hadm : IsAdmissible π) (hirr : Representation.IsIrreducible π) :
    (inverseTransposePullback π).Equiv (smoothContragredient π) := by
  let h := gelfandKazhdanContragredient p inferInstance F n V π hadm hirr
  exact Representation.Equiv.mk h.choose (fun g => LinearMap.ext (h.choose_spec g))

/-- Full functional-space transport to the actual smooth dual, with character
reversal, using the existing long-Weyl transform and the chosen equivalence. -/
def smoothDualFunctionalEquiv (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hadm : IsAdmissible π) (hirr : Representation.IsIrreducible π) :
    glFunctionals ψ n π ≃ₗ[ℂ] glInverseFunctionals ψ n (smoothContragredient π) :=
  (dualFunctionalEquiv π ψ).trans
    (Langlands.Whittaker.functionalsCongr
      (inverseTransposeSmoothDualEquiv F π hadm hirr))

/-- The reverse-character version of the same functional-space construction. -/
def smoothDualInverseFunctionalEquiv (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hadm : IsAdmissible π) (hirr : Representation.IsIrreducible π) :
    glInverseFunctionals ψ n π ≃ₗ[ℂ] glFunctionals ψ n (smoothContragredient π) :=
  (dualInverseFunctionalEquiv π ψ).trans
    (Langlands.Whittaker.functionalsCongr
      (inverseTransposeSmoothDualEquiv F π hadm hirr))

/-- The constructed functional evaluates by inverse equivalence after long-Weyl
translation. No normalization of the chosen Gelfand–Kazhdan equivalence is asserted. -/
theorem smoothDualFunctionalEquiv_apply (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hadm : IsAdmissible π) (hirr : Representation.IsIrreducible π)
    (ℓ : glFunctionals ψ n π) (v : SmoothDual π) :
    (smoothDualFunctionalEquiv F π ψ hadm hirr ℓ).val v =
      ℓ.val (π (weylLong (n + 1) F.Carrier)
        ((inverseTransposeSmoothDualEquiv F π hadm hirr).symm v)) := rfl

/-- All clauses of Whittaker type transport to the actual smooth dual of an
irreducible representation. The source type supplies admissibility. -/
theorem isOfWhittakerType_smoothContragredient
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hirr : Representation.IsIrreducible π) :
    IsOfWhittakerType n (inverseStandardCharacter ψ n) (smoothContragredient π) :=
  (isOfWhittakerType_inverseTransposePullback ψ π hπ).of_equiv
    (inverseTransposeSmoothDualEquiv F π hπ.1 hirr)

/-- Inverse-standard Whittaker type transports in the opposite character direction. -/
theorem isOfWhittakerType_smoothContragredient_inverse
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hπ : IsOfWhittakerType n (inverseStandardCharacter ψ n) π)
    (hirr : Representation.IsIrreducible π) :
    IsOfWhittakerType n (standardCharacter ψ n) (smoothContragredient π) :=
  (isOfWhittakerType_inverseTransposePullback_inverse ψ π hπ).of_equiv
    (inverseTransposeSmoothDualEquiv F π hπ.1 hirr)

end Equivalence

section Pair

local instance : MeasurableSpace F.Carrier := borel F.Carrier

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  (hπ : IsAdmissible π) (hσ : IsAdmissible σ)
  (hirrπ : Representation.IsIrreducible π) (hirrσ : Representation.IsIrreducible σ)
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F.Carrier}
  {abv : AbsoluteValue F.Carrier ℝ}
  [MeasurableSpace (LeftUnipotentQuotient n F.Carrier)]
  {μ : Measure (LeftUnipotentQuotient n F.Carrier)}
  {ν : AdditiveHaarMeasure F.Carrier}

include hπ hσ hirrπ hirrσ

/-- The inverse-transpose dual-pair polynomial is exactly the polynomial of the
actual smooth-dual pair, with the same measures and the reversed character. -/
theorem isDualPairLPolynomial_iff_smoothContragredient {P : ℂ[X]} :
    IsDualPairLPolynomial q ψ abv μ ν π σ P ↔
      IsPairLPolynomial q (ψ.scale (-1)) abv μ ν
        (smoothContragredient π) (smoothContragredient σ) P :=
  isPairLPolynomial_congr_equiv
    (inverseTransposeSmoothDualEquiv F π hπ hirrπ)
    (inverseTransposeSmoothDualEquiv F σ hσ hirrσ)

/-- Existence transports to the genuine smooth-dual pair in both directions. -/
theorem dualPairLPolynomialExists_iff_smoothContragredient :
    DualPairLPolynomialExists q ψ abv μ ν π σ ↔
      PairLPolynomialExists q (ψ.scale (-1)) abv μ ν
        (smoothContragredient π) (smoothContragredient σ) :=
  exists_congr fun _ =>
    isDualPairLPolynomial_iff_smoothContragredient F hπ hσ hirrπ hirrσ

/-- Construct the L-factor of the actual smooth-dual pair from explicit
existence for the existing inverse-transpose dual pair. -/
def smoothDualPairLFactor (h : DualPairLPolynomialExists q ψ abv μ ν π σ) :
    RationalFunctionsˣ :=
  pairLFactor
    ((dualPairLPolynomialExists_iff_smoothContragredient F hπ hσ hirrπ hirrσ).mp h)

/-- The constructed factor is the reciprocal of any certified polynomial of the
actual smooth-dual pair. -/
theorem smoothDualPairLFactor_eq (h : DualPairLPolynomialExists q ψ abv μ ν π σ)
    {P : ℂ[X]} (hP : IsPairLPolynomial q (ψ.scale (-1)) abv μ ν
      (smoothContragredient π) (smoothContragredient σ) P) :
    (smoothDualPairLFactor F hπ hσ hirrπ hirrσ h : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ :=
  pairLFactor_eq _ hP

/-- The constructed actual smooth-dual factor equals the existing
inverse-transpose dual-pair factor as a rational-function unit. -/
theorem smoothDualPairLFactor_eq_dualPairLFactor
    (h : DualPairLPolynomialExists q ψ abv μ ν π σ) :
    smoothDualPairLFactor F hπ hσ hirrπ hirrσ h = dualPairLFactor h := by
  apply Units.ext
  rw [smoothDualPairLFactor_eq F hπ hσ hirrπ hirrσ h
    ((isDualPairLPolynomial_iff_smoothContragredient F hπ hσ hirrπ hirrσ).mp
      (pairLPolynomial_spec h))]
  exact (dualPairLFactor_eq h (pairLPolynomial_spec h)).symm

end Pair

section Symmetric

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  (hπ : IsAdmissible π) (hσ : IsAdmissible σ)
  (hirrπ : Representation.IsIrreducible π) (hirrσ : Representation.IsIrreducible σ)
  {ψ : UnitaryAdditiveCharacter F.Carrier}
  {ν : @AdditiveHaarMeasure F.Carrier _ _ (borel F.Carrier)}

include hπ hσ hirrπ hirrσ

/-- The existing p-adic L relation can use actual smooth contragredients in either
rank order. The caller chooses the character, including its inverse if needed. -/
theorem isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient
    {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν
      (inverseTransposePullback π) (inverseTransposePullback σ) P ↔
    IsPadicSymmetricLPolynomial F ψ ν
      (smoothContragredient π) (smoothContragredient σ) P :=
  IsPadicSymmetricLPolynomial.congr_equiv
    (inverseTransposeSmoothDualEquiv F π hπ hirrπ)
    (inverseTransposeSmoothDualEquiv F σ hσ hirrσ)

/-- The same actual equivalences transport the existing epsilon relation. -/
theorem isPadicSymmetricEpsilonFactor_inverseTranspose_iff_smoothContragredient
    {e : ℂˣ × ℤ} :
    IsPadicSymmetricEpsilonFactor F ψ ν
      (inverseTransposePullback π) (inverseTransposePullback σ) e ↔
    IsPadicSymmetricEpsilonFactor F ψ ν
      (smoothContragredient π) (smoothContragredient σ) e :=
  IsPadicSymmetricEpsilonFactor.congr_equiv
    (inverseTransposeSmoothDualEquiv F π hπ hirrπ)
    (inverseTransposeSmoothDualEquiv F σ hσ hirrσ)

/-- The same actual equivalences transport the existing gamma relation. -/
theorem isPadicSymmetricGammaFactor_inverseTranspose_iff_smoothContragredient
    {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν
      (inverseTransposePullback π) (inverseTransposePullback σ) G ↔
    IsPadicSymmetricGammaFactor F ψ ν
      (smoothContragredient π) (smoothContragredient σ) G :=
  IsPadicSymmetricGammaFactor.congr_equiv
    (inverseTransposeSmoothDualEquiv F π hπ hirrπ)
    (inverseTransposeSmoothDualEquiv F σ hσ hirrσ)

end Symmetric

end Langlands.RankinSelberg
