import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.HarmonicAnalysis.Conductor

/-!
# Normalizations of epsilon factors of pairs

Bushnell and Henniart 1999, Théorème 2 (printed page 538): for an irreducible
admissible representation `π` of `GL_n(F)` with central character `ω_π`,
`ε(π × π̌, ψ, 1/2) = ω_π(-1)^(n-1)`. Bushnell, Henniart and Kutzko 1998,
introduction (printed page 703): for irreducible smooth `π₁` of `GL_(n₁)(F)` and
`π₂` of `GL_(n₂)(F)`, `ε(π₁ × π₂, s, ψ) = ε(π₁ × π₂, 0, ψ) q^(-f(π₁ × π₂, ψ) s)`
with `f(π₁ × π₂, ψ) = n₁ n₂ c(ψ) + f(π₁ × π₂)`, where `f(π₁ × π₂)` does not
depend on `ψ`. The epsilon factors are the JPSS relations
`IsPadicPairEpsilonFactor` and `IsPadicSymmetricEpsilonFactor` with the
self-dual measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- Bushnell and Henniart 1999, Théorème 2 (printed page 538; also the abstract,
printed page 534), for generic representations: let `π` be an irreducible
admissible representation of `GL_(r+1)(F)` with a nonzero standard Whittaker
functional for `ψ` and central character `ω`. Then the pair `(π, π̌)`, `π̌` the
smooth contragredient, has an epsilon factor `ε(s, π × π̌, ψ) = c q^(-ms)`,
`e = (c, m)`, and its value at `s = 1/2` is `ω(-1)^r`. -/
def ContragredientEpsilonCentralValueStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π) →
    Classification.HasGLCentralCharacter F.Carrier (r + 1) π ω →
    ∃ e : ℂˣ × ℤ,
      (letI := F.canonicalTopologicalData.topology
       haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
       IsPadicPairEpsilonFactor F ψ ν.val π (smoothContragredient π) e) ∧
      (e.1 : ℂ) * (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(e.2 : ℂ) / 2) =
        ((ω (-1) : ℂˣ) : ℂ) ^ r

/-- Bushnell, Henniart and Kutzko 1998, introduction (printed page 703; also the
Comments to 5.1, printed page 718): let `π` and `σ` be irreducible admissible
representations of `GL_(r+1)(F)` and `GL_(t+1)(F)`. There is an integer `a`,
the exponent `f(π × σ)`, such that for every additive character `ψ`, every
measure `ν` self-dual for `ψ` and every epsilon factor
`ε(s, π × σ, ψ) = c q^(-ms)` of the pair, `m = a + (r+1)(t+1) n(ψ)`, where
`n(ψ)` is the additive conductor exponent: the largest `k` with `ψ` trivial on
`p^(-k)`. -/
def PairEpsilonExponentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    Representation.IsIrreducible π →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible π) →
    Representation.IsIrreducible σ →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible σ) →
    ∃ a : ℤ, ∀ (ψ : letI := F.canonicalTopologicalData.topology;
        UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (e : ℂˣ × ℤ),
      IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e →
        e.2 = a + ((r + 1) * (t + 1) : ℕ) * F.canonicalTopologicalData.additiveConductor ψ

/-- The normalizations of epsilon factors of pairs: the central value of
`ε(s, π × π̌, ψ)` (Bushnell–Henniart 1999, Théorème 2) and the dependence of the
exponent on the conductor of `ψ` (Bushnell–Henniart–Kutzko 1998). -/
def PairEpsilonNormalizationStatement : Prop :=
  ContragredientEpsilonCentralValueStatement.{uF, uV} ∧
    PairEpsilonExponentStatement.{uF, uV, uW}

end Langlands.RankinSelberg
