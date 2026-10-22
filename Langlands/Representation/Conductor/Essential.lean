import Langlands.Representation.Conductor.SphericalTests
import Langlands.Representation.Whittaker.Spherical
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.RankinSelberg.RankOneQuotient
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-!
# Jacquet's corrected essential vector on `GL_(n+2)`

A Whittaker function `W` of `π` on `GL_(n+2)` is essential when, for every tuple `x` of
nonzero Satake parameters, the corank-one integral of `W` against the spherical
Whittaker function `W(g; x; ψ̄)` of `GL_(n+1)` converges on a right half-plane and
continues to `∏ i, P(x_i q^(-s))⁻¹`, where `L(s, π) = P(q^(-s))⁻¹`, and its restriction
to `diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant. Neither existence nor
uniqueness is asserted; the vector is selected only from a unique-existence proof.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-! ### Additive characters of conductor `O` -/

/-- `ψ` has conductor `O`: it is trivial on `O`, and `ψ(x O) = 1` only for `x ∈ O`. -/
def HasIntegerConductor (ψ : UnitaryAdditiveCharacter F) : Prop :=
  (∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1) ∧
    ∀ x : F, (∀ y ∈ (ValuativeRel.valuation F).integer, ψ (x * y) = 1) →
      x ∈ (ValuativeRel.valuation F).integer

/-! ### The spherical Whittaker function for `ψ̄` -/

section Spherical

variable {ψ : UnitaryAdditiveCharacter F} {n : ℕ}

/-- Jacquet's `W(g; x; ψ̄)` on `GL_(n+1)`: the explicit spherical Whittaker function for
the inverse standard character, as an inverse-character Whittaker function. -/
def inverseSphericalWhittaker (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (q : ℕ)
    (x : Fin (n + 1) → ℂˣ) : InverseWhittakerFunctions ψ n :=
  ⟨sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q x,
    sphericalWhittaker_mem hϖ q x (isIntegrallyTrivial_inverseStandardCharacter hψ n)⟩

variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
  {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (q : ℕ)
  (x : Fin (n + 1) → ℂˣ)

@[simp] theorem inverseSphericalWhittaker_apply (g : Langlands.GeneralLinear (n + 1) F) :
    (inverseSphericalWhittaker hψ hϖ q x).val g =
      sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q x g := rfl

theorem inverseSphericalWhittaker_one : (inverseSphericalWhittaker hψ hϖ q x).val 1 = 1 :=
  sphericalWhittaker_one hϖ q x (isIntegrallyTrivial_inverseStandardCharacter hψ n)

theorem inverseSphericalWhittaker_mul_integral (g : Langlands.GeneralLinear (n + 1) F)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    (inverseSphericalWhittaker hψ hϖ q x).val (g * k) =
      (inverseSphericalWhittaker hψ hϖ q x).val g :=
  sphericalWhittaker_mul_integral hϖ q x (isIntegrallyTrivial_inverseStandardCharacter hψ n) g hk

end Spherical

/-! ### The right-hand side `∏ i, P(x_i X)⁻¹` -/

/-- Jacquet's `∏ i, P(q^(-s) x_i)⁻¹` as a rational function of `X = q^(-s)`. -/
def essentialFactor {m : ℕ} (P : ℂ[X]) (x : Fin m → ℂˣ) : RationalFunctions :=
  ∏ i, (algebraMap ℂ[X] RationalFunctions (P.comp (C (x i : ℂ) * X)))⁻¹

/-- The factor is the reciprocal of the single polynomial `∏ i, P(x_i X)`. -/
theorem essentialFactor_eq {m : ℕ} (P : ℂ[X]) (x : Fin m → ℂˣ) :
    essentialFactor P x =
      (algebraMap ℂ[X] RationalFunctions (∏ i, P.comp (C (x i : ℂ) * X)))⁻¹ := by
  rw [essentialFactor, map_prod, Finset.prod_inv_distrib]

/-! ### Jacquet's identity for a single Whittaker function -/

section Identity

variable {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable (μ : Measure (LeftUnipotentQuotient n F))

/-- The identity of Jacquet's Theorem 1 for `W` on `GL_(n+2)` and a polynomial `P`: for
every `x`, the corank-one integral of `W` against `W(g; x; ψ̄)` converges on a right
half-plane and has the rational continuation `∏ i, P(x_i X)⁻¹`. -/
def SatisfiesEssentialIdentity (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (P : ℂ[X])
    (W : WhittakerFunctions ψ (n + 1)) : Prop :=
  ∀ x : Fin (n + 1) → ℂˣ,
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x) s) ∧
    HasRationalContinuation q
      (corankOneIntegral ψ abv μ W (inverseSphericalWhittaker hψ hϖ q x))
      (essentialFactor P x)

end Identity

/-! ### Jacquet's normalizations and the essential vector -/

section Essential

variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]

/-- The normalizations of Jacquet's Theorem 1 on `GL_(n+1)`: `q` is the residue
cardinality, `ϖ` is a uniformizing element, `abv` is the normalized absolute value
(`|ϖ| = q⁻¹`, trivial on valuation units), `ψ` has conductor `O`, and `μ` is the quotient
measure compatible with the Haar measures giving `GL_(n+1)(O)` and `N_(n+1)(O)` mass one.
The quotients `N_(n+1) \ GL_(n+1)` and `N_1 \ GL_1` carry their Borel σ-algebras. -/
structure IsJacquetNormalization (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ϖ : Fˣ) (μ : Measure (LeftUnipotentQuotient n F)) : Prop where
  residueCardinality :
    q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)
  uniformizer : IsUniformizingElement (ValuativeRel.valuation F) ϖ
  abv_uniformizer : abv (ϖ : F) = (q : ℝ)⁻¹
  abv_unit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1
  conductor : HasIntegerConductor ψ
  measure : QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F)
    (generalLinearHaar F n) (unipotentHaar F n) μ
  borel : BorelSpace (LeftUnipotentQuotient n F)
  borel_rankOne : BorelSpace (LeftUnipotentQuotient 0 F)

variable [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}

/-- Jacquet's essential vector in the model of `ℓ`: Theorem 1's identity holds with the
standard L-polynomial `P` of `π`, `L(s, π × 1) = P(q^(-s))⁻¹`, and the restriction of `w`
to `diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant. -/
def IsEssentialVector (h : IsJacquetNormalization q ψ abv ϖ μ)
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + 1) π) (w : (coefficientModel π ℓ).toSubmodule) : Prop :=
  (∃ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P ∧
      SatisfiesEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P w.val) ∧
    IsIntegralInvariantOnRestriction π ℓ w

variable (h : IsJacquetNormalization q ψ abv ϖ μ)
  (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
  (ℓ : glFunctionals ψ (n + 1) π)

/-- An essential vector satisfies the identity for every standard L-polynomial, which is
unique. -/
theorem IsEssentialVector.satisfiesEssentialIdentity {w : (coefficientModel π ℓ).toSubmodule}
    (hw : IsEssentialVector h π ℓ w) {P : ℂ[X]}
    (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P) :
    SatisfiesEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P w.val := by
  obtain ⟨⟨P', hP', hid⟩, _⟩ := hw
  rwa [IsNormalizedGenerator.unique hP hP']

/-- The essential vector, selected only from a proof that exactly one vector of the
model of `ℓ` is essential. -/
def essentialVector (hu : ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w) :
    (coefficientModel π ℓ).toSubmodule :=
  Classical.choose hu.exists

theorem essentialVector_spec
    (hu : ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w) :
    IsEssentialVector h π ℓ (essentialVector h π ℓ hu) :=
  Classical.choose_spec hu.exists

theorem isEssentialVector_iff_eq
    (hu : ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w)
    (w : (coefficientModel π ℓ).toSubmodule) :
    IsEssentialVector h π ℓ w ↔ w = essentialVector h π ℓ hu :=
  ⟨fun hw => hu.unique hw (essentialVector_spec h π ℓ hu),
    fun hw => hw ▸ essentialVector_spec h π ℓ hu⟩

end Essential

end Langlands.Conductor
