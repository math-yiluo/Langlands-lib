import Langlands.Representation.RankinSelberg.UnramifiedPairStatement
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Hecke.TestFunction
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Unramified local factors of pairs

Cogdell, *Analytic theory of L-functions for GL_n* (in Bernstein–Gelbart, *An
introduction to the Langlands program*), Theorem 3.3, printed page 215, and Cogdell,
*Lectures on L-functions, converse theorems, and functoriality for GL_n* (Fields
Institute lectures), Lecture 7, Theorem 7.1 and Corollaries 7.1.1 and 7.1.2, printed
page 58. Let `π` and `σ` be irreducible admissible unitary generic unramified
representations of `GL_n(F)` and `GL_m(F)` with Langlands classes `A` and `A'`, and let
`ψ` have conductor `O`. For `m = n` the integral of the normalized spherical vectors
against the characteristic function of `O^n` is `det(1 - A ⊗ A' q^(-s))⁻¹`; for all
ranks `L(s, π × σ) = det(1 - A ⊗ A' q^(-s))⁻¹` and `ε(s, π × σ, ψ) ≡ 1`. The Langlands
parameters of a unitary generic unramified representation satisfy the Jacquet–Shalika
bounds `q^(-1/2) < |χ_i(ϖ)| < q^(1/2)`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Langlands.Conductor Polynomial
open Langlands.Correspondence

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- The characteristic function `Φ°` of the lattice `O^(n+1)` in the row space
`F^(n+1)`, for the integer ring `O` of the canonical valuation. -/
def integerLatticeIndicator (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    SchwartzBruhat (Fin (n + 1) → F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  Hecke.TestFunction.characteristic
    (s := Set.univ.pi fun _ : Fin (n + 1) =>
      (F.canonicalTopologicalData.Integers : Set F.Carrier))
    ⟨isClosed_set_pi fun _ _ => (ValuativeRel.valuation F.Carrier).isClosed_integer,
      isOpen_set_pi Set.finite_univ fun _ _ =>
        (ValuativeRel.valuation F.Carrier).isOpen_integer⟩
    (isCompact_univ_pi fun _ => F.canonicalTopologicalData.isCompact_integers)

/-- The polynomial `det(1 - (A ⊗ A') X) = ∏_(i,j) (1 - a_i a'_j X)` of the eigenvalue
tuples `a` of `A` and `a'` of `A'`. -/
def unramifiedLPolynomial {m m' : ℕ} (a : Fin m → ℂ) (a' : Fin m' → ℂ) : ℂ[X] :=
  ∏ i, ∏ j, (1 - C (a i * a' j) * X)

/-- Cogdell, Analytic theory, Theorem 3.3 (case `m = n`, printed page 215), and Cogdell,
Fields lectures, Lecture 7, the sentence after Theorem 7.1 (printed page 58: the same
result holds for `GL_n × GL_n` with `Φ°` the characteristic function of `O^n`). Let `π`
and `σ` be unitary unramified generic representations of `GL_(n+1)(F)` with Langlands
classes `A = diag(χ_i(ϖ))` and `A' = diag(χ'_j(ϖ))`, and take Jacquet's normalizations
(`q` the residue cardinality, the normalized absolute value, `ψ` of conductor `O`, and the
quotient measure on `N_(n+1) \ GL_(n+1)` from the Haar measures giving `GL_(n+1)(O)` and
`N_(n+1)(O)` mass one). For the normalized spherical vectors `W₀` of a `ψ`-Whittaker
model of `π` and `W₀'` of a `ψ⁻¹`-Whittaker model of `σ`, the integral
`Ψ(s, W₀, W₀', Φ°) = ∫ W₀(g) W₀'(g) Φ°(e_(n+1) g) |det g|^s dg` converges for `Re s`
large and equals `det(1 - A ⊗ A' q^(-s))⁻¹`. -/
def UnramifiedEqualRankIntegralStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (χ χ' : Fin (n + 1) → QuasiCharacter F) (q : ℕ)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
    (μ : letI := F.canonicalTopologicalData.topology
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier)),
    IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
    IsUnitarizable π → IsUnitarizable σ →
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI := borel (LeftUnipotentQuotient 0 F.Carrier)
    IsJacquetNormalization q ψ abv ϖ μ →
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      ∀ (w : SphericalTest π ℓ) (w' : SphericalTest σ ℓ'),
        ∃ c : ℝ, ∀ s : ℂ, c < s.re →
          EqualRankConverges ψ abv μ w.val.val.val w'.val.val.val
              (integerLatticeIndicator F n) s ∧
          equalRankModelIntegral ψ abv μ π σ ℓ ℓ' w.val.val w'.val.val
              (integerLatticeIndicator F n) s =
            unramifiedEulerFactor q (unramifiedClass F χ) (unramifiedClass F χ') s

/-- Cogdell, Analytic theory, Theorem 3.3 (printed page 215), and Cogdell, Fields
lectures, Theorem 7.1 (printed page 58): let `π` and `σ` be unitary unramified generic
representations of `GL_(r+1)(F)` and `GL_(n+1)(F)`, in either rank order, with Langlands
classes `A = diag(χ_i(ϖ))` and `A' = diag(χ'_j(ϖ))`, and let `ψ` have conductor `O`. Then
`L(s, π × σ) = det(1 - A ⊗ A' q^(-s))⁻¹`: for every additive Haar measure `ν`, the
L-polynomial of the pair is `∏_(i,j) (1 - χ_i(ϖ) χ'_j(ϖ) X)`. -/
def UnramifiedPairLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (χ : Fin (r + 1) → QuasiCharacter F) (χ' : Fin (n + 1) → QuasiCharacter F)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier),
    (letI := F.canonicalTopologicalData.topology
     letI := F.canonicalTopologicalData.valuativeRel
     HasIntegerConductor ψ) →
    IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
    IsUnitarizable π → IsUnitarizable σ →
    IsPadicSymmetricLPolynomial F ψ ν π σ
      (unramifiedLPolynomial (unramifiedClass F χ) (unramifiedClass F χ'))

/-- Cogdell, Analytic theory, Theorem 3.3 (printed page 215), and Cogdell, Fields
lectures, Corollary 7.1.1 (printed page 58): for `π`, `σ` and `ψ` as in
`UnramifiedPairLFactorStatement` and `ν` the Haar measure self-dual for `ψ`,
`ε(s, π × σ, ψ) ≡ 1`, that is, `ε = c q^(-ms)` with `(c, m) = (1, 0)`. -/
def UnramifiedPairEpsilonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (χ : Fin (r + 1) → QuasiCharacter F) (χ' : Fin (n + 1) → QuasiCharacter F)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    (letI := F.canonicalTopologicalData.topology
     letI := F.canonicalTopologicalData.valuativeRel
     HasIntegerConductor ψ) →
    IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
    IsUnitarizable π → IsUnitarizable σ →
    IsPadicSymmetricEpsilonFactor F ψ ν.val π σ (1, 0)

/-- Cogdell, Fields lectures, Corollary 7.1.2 (printed page 58), the Jacquet–Shalika
bounds: for an irreducible unitary generic unramified representation `π` of
`GL_(r+1)(F)` with Langlands class `diag(χ_i(ϖ))`, `q^(-1/2) < |χ_i(ϖ)| < q^(1/2)` for
every `i`, `q` the residue cardinality. -/
def UnramifiedUnitaryParameterBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : Fin (r + 1) → QuasiCharacter F)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier),
    IsUnramifiedGenericConstituent F ψ π χ → IsUnitarizable π →
    ∀ i, (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(1 / 2 : ℝ)) <
        ‖unramifiedClass F χ i‖ ∧
      ‖unramifiedClass F χ i‖ <
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (1 / 2 : ℝ)

/-- The unramified local factors of pairs and the Jacquet–Shalika bounds: Cogdell,
Analytic theory, Theorem 3.3, and Cogdell, Fields lectures, Theorem 7.1 and
Corollaries 7.1.1 and 7.1.2. -/
def UnramifiedFactorStatement : Prop :=
  UnramifiedEqualRankIntegralStatement.{uF, uV, uW} ∧
    UnramifiedPairLFactorStatement.{uF, uV, uW} ∧
    UnramifiedPairEpsilonStatement.{uF, uV, uW} ∧
    UnramifiedUnitaryParameterBoundStatement.{uF, uV}

end Langlands.RankinSelberg
