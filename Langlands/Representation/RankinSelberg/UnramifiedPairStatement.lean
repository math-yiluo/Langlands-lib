import Langlands.Representation.Conductor.Essential
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.Unitary.Basic

/-!
# The unramified computation of Rankin–Selberg integrals

Jacquet and Shalika, *On Euler products and the classification of automorphic
forms II*, §1.3–§1.5, printed pages 780–782. For an unramified generic
representation `π` of `GL_r(F)` and `ψ` of conductor `O`, the Whittaker model of `π`
has, up to scalars, exactly one right `GL_r(O)`-invariant vector `W₀`, and
`W₀(e) ≠ 0` (§1.3). For `r > r'`, unramified generic `π`, `π'` with Langlands classes
`A`, `A'`, and the normalized spherical vectors `W₀`, `W₀'`,
`Ψ(s, W₀, W₀') = det(1 - A ⊗ A' q^(-s))⁻¹` (§1.4 (3)), and when `π`, `π'` are
unitary this Euler factor has no pole in `Re s ≥ 1` (Proposition 1.5(iii)).
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Langlands.Conductor
open Langlands.Correspondence

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- The Langlands class `diag(χ_1(ϖ), …, χ_m(ϖ))` of the unramified quasi-characters
`χ_i`, for the canonical uniformizer `ϖ` of `F`, as its tuple of eigenvalues. -/
def unramifiedClass (F : PadicField.{uF} p) {m : ℕ} (χ : Fin m → QuasiCharacter F) :
    Fin m → ℂ :=
  letI := F.canonicalTopologicalData.topology
  fun i => ((χ i).toMonoidHom F.canonicalTopologicalData.uniformizerUnit : ℂ)

/-- The Euler factor `det(1 - A ⊗ A' q^(-s))⁻¹ = ∏_(i,j) (1 - a_i a'_j q^(-s))⁻¹` of
the eigenvalue tuples `a` of `A` and `a'` of `A'`. -/
def unramifiedEulerFactor (q : ℕ) {m m' : ℕ} (a : Fin m → ℂ) (a' : Fin m' → ℂ) (s : ℂ) :
    ℂ :=
  (∏ i, ∏ j, (1 - a i * a' j * (q : ℂ) ^ (-s)))⁻¹

/-- `π` is an unramified generic representation of `GL_(r+1)(F)` with Langlands class
`diag(χ_i(ϖ))`: it is generic for `ψ` (irreducible, admissible, with a nonzero
standard Whittaker functional), it has a nonzero `GL_(r+1)(O)`-fixed vector, the `χ_i`
are unramified, and `π` is a subquotient of the normalized principal series
`i(χ_1, …, χ_(r+1))`. -/
def IsUnramifiedGenericConstituent (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : Fin (r + 1) → QuasiCharacter F) : Prop :=
  (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π) ∧
    fixedVectors π (sphericalSubgroup F r) ≠ ⊥ ∧
    (letI := F.canonicalTopologicalData.topology
     ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) ∧
    IsSubquotientOf (principalSeries F r χ) π

/-- Jacquet–Shalika, Euler products II, §1.3, printed page 780: let `π` be an
irreducible admissible generic representation of `GL_(r+1)(F)` with a nonzero
`GL_(r+1)(O)`-fixed vector, and let `ψ` have conductor `O`. Then every Whittaker model
of `π` (for `ψ`, and also for `ψ⁻¹`, which has conductor `O` as well) contains exactly
one right `GL_(r+1)(O)`-invariant function `W₀` with `W₀(e) = 1`. -/
def UnramifiedSphericalVectorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier),
    (letI := F.canonicalTopologicalData.topology
     letI := F.canonicalTopologicalData.valuativeRel
     HasIntegerConductor ψ) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π) →
    fixedVectors π (sphericalSubgroup F r) ≠ ⊥ →
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    (∀ ℓ : glFunctionals ψ r π, ℓ.val ≠ 0 →
      ∃ w : SphericalTest π ℓ, ∀ w' : SphericalTest π ℓ, w' = w) ∧
    (∀ ℓ : glInverseFunctionals ψ r π, ℓ.val ≠ 0 →
      ∃ w : SphericalTest π ℓ, ∀ w' : SphericalTest π ℓ, w' = w)

/-- Jacquet–Shalika, Euler products II, §1.4, printed pages 780–781, display (3): let
`r = n + k + 2 > r' = n + 1`, let `π` and `σ` be unramified generic representations of
`GL_r(F)` and `GL_(r')(F)` with Langlands classes `A = diag(χ_i(ϖ))` and
`A' = diag(χ'_j(ϖ))`, and take Jacquet's normalizations (`q` the residue cardinality,
the normalized absolute value, `ψ` of conductor `O`, and the quotient measure on
`N_(r') \ GL_(r')` from the Haar measures giving `GL_(r')(O)` and `N_(r')(O)` mass one).
For the normalized spherical vectors `W₀` of a `ψ`-Whittaker model of `π` and `W₀'` of
a `ψ⁻¹`-Whittaker model of `σ`, the integral
`Ψ(s, W₀, W₀') = ∫ W₀(diag(g, 1_(k+1))) W₀'(g) |det g|^(s - (k+1)/2) dg`
converges for `Re s` large and equals `det(1 - A ⊗ A' q^(-s))⁻¹`. -/
def UnramifiedPairIntegralStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (χ : Fin (n + (0 + k + 1) + 1) → QuasiCharacter F) (χ' : Fin (n + 1) → QuasiCharacter F)
    (q : ℕ)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
    (μ : letI := F.canonicalTopologicalData.topology
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier)),
    IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
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
    ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      ∀ (w : SphericalTest π ℓ) (w' : SphericalTest σ ℓ'),
        ∃ c : ℝ, ∀ s : ℂ, c < s.re →
          UnequalRankConverges ψ abv 0 k μ (Measure.dirac 0) w.val.val.val w'.val.val.val s ∧
          unequalRankModelIntegral ψ abv 0 k μ (Measure.dirac 0) π σ ℓ ℓ' w.val.val
              w'.val.val s =
            unramifiedEulerFactor q (unramifiedClass F χ) (unramifiedClass F χ') s

/-- Jacquet–Shalika, Euler products II, Proposition 1.5(iii), printed page 782: for
`r = t + 1 > r' = n + 1` and unramified generic representations `π`, `σ` as in
`UnramifiedPairIntegralStatement` that are unitary (unitarizable), the Euler factor
`L(s, π × σ) = det(1 - A ⊗ A' q^(-s))⁻¹` has no pole in `Re s ≥ 1`. -/
def UnramifiedUnitaryPoleFreeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (t n : ℕ),
    n < t →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W]
      [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (χ : Fin (t + 1) → QuasiCharacter F) (χ' : Fin (n + 1) → QuasiCharacter F)
      (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier),
      IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
      IsUnitarizable π → IsUnitarizable σ →
      ∀ s : ℂ, 1 ≤ s.re →
        ∏ i, ∏ j, (1 - unramifiedClass F χ i * unramifiedClass F χ' j *
          (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s)) ≠ 0

/-- The unramified computation of Jacquet–Shalika, Euler products II, §1.3–§1.5. -/
def UnramifiedPairStatement : Prop :=
  UnramifiedSphericalVectorStatement.{uF, uV} ∧
    UnramifiedPairIntegralStatement.{uF, uV, uW} ∧
    UnramifiedUnitaryPoleFreeStatement.{uF, uV, uW}

end Langlands.RankinSelberg
