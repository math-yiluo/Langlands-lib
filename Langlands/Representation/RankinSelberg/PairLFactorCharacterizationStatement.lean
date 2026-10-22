import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Classification.Supercuspidal

/-!
# Characterizations by L-factors of pairs

Henniart 2002, Théorème 1.6(b), (i) ⇔ (ii), and Théorème 1.7(b), printed pages
590-591. An irreducible representation `π` of `GL_n(F)`, `n ≥ 2`, is
supercuspidal exactly when `L(s, π × ρ) = 1` for every supercuspidal `ρ` of
`GL_r(F)`, `1 ≤ r ≤ n - 1`. A non-supercuspidal irreducible `π` is determined by
the orders of the poles at `s = 0` of `L(s, π × ρ)` for the essentially
square-integrable `ρ` of `GL_r(F)`, `1 ≤ r ≤ n - 1`. The L-factors are those of
every irreducible admissible pair, `IsLanglandsPairLPolynomial`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- The order of the pole at `s = 0` of `L(s) = 1 / P(q^(-s))`: the multiplicity
of `1` as a root of `P` (zero when `P = 0`, which no L-polynomial is). -/
def lPolynomialPoleOrderAtZero (P : ℂ[X]) : ℕ :=
  P.rootMultiplicity 1

/-- Henniart 2002, Théorème 1.6(b), (i) ⇔ (ii), printed pages 590-591: an
irreducible admissible representation `π` of `GL_(n+2)(F)` is supercuspidal if
and only if `L(s, π × ρ) = 1` for every irreducible supercuspidal
representation `ρ` of `GL_(r+1)(F)`, `r ≤ n`. -/
def SupercuspidalLFactorCharacterizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 2) F.Carrier)),
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible π.representation) →
    (letI := F.canonicalTopologicalData.topology; π.IsAdmissible) →
    ((letI := F.canonicalTopologicalData.topology;
        GeneralLinear.IsSupercuspidal π.representation) ↔
      ∀ (r : ℕ), r ≤ n →
        ∀ ρ : letI := F.canonicalTopologicalData.topology
            SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier),
          (letI := F.canonicalTopologicalData.topology;
            Representation.IsIrreducible ρ.representation) →
          (letI := F.canonicalTopologicalData.topology;
            GeneralLinear.IsSupercuspidal ρ.representation) →
          IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π ρ 1)

/-- Henniart 2002, Théorème 1.7(b), printed page 591: let `π` and `π'` be
irreducible admissible representations of `GL_(n+2)(F)`, `π` not supercuspidal.
If for every irreducible essentially square-integrable representation `ρ` of
`GL_(r+1)(F)`, `r ≤ n`, the factors `L(s, π × ρ)` and `L(s, π' × ρ)` have poles
of the same order at `s = 0`, then `π ≃ π'`. -/
def SquareIntegrablePoleOrderCharacterizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ)
    (π π' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 2) F.Carrier)),
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible π.representation) →
    (letI := F.canonicalTopologicalData.topology; π.IsAdmissible) →
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible π'.representation) →
    (letI := F.canonicalTopologicalData.topology; π'.IsAdmissible) →
    ¬ (letI := F.canonicalTopologicalData.topology;
      GeneralLinear.IsSupercuspidal π.representation) →
    (∀ (r : ℕ), r ≤ n →
      ∀ ρ : letI := F.canonicalTopologicalData.topology
          SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier),
        (letI := F.canonicalTopologicalData.topology;
          Representation.IsIrreducible ρ.representation) →
        (letI := F.canonicalTopologicalData.topology;
          F.canonicalTopologicalData.IsEssentiallySquareIntegrable ρ.representation) →
        ∃ P P' : ℂ[X], IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π ρ P ∧
          IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π' ρ P' ∧
          lPolynomialPoleOrderAtZero P = lPolynomialPoleOrderAtZero P') →
    (letI := F.canonicalTopologicalData.topology;
      Nonempty (π.representation.Equiv π'.representation))

/-- Henniart 2002, Théorèmes 1.6(b) ((i) ⇔ (ii)) and 1.7(b): the
characterizations of supercuspidal and of all irreducible representations by
L-factors of pairs. -/
def PairLFactorCharacterizationStatement : Prop :=
  SupercuspidalLFactorCharacterizationStatement.{uF, uV, uW} ∧
    SquareIntegrablePoleOrderCharacterizationStatement.{uF, uV, uW}

end Langlands.RankinSelberg
