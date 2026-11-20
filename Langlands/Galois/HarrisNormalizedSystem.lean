import Langlands.Galois.ClozelSelfDualStatements
import Langlands.Galois.WeakAssociation

/-!
# Arithmetic polynomial systems for the cuspidal Harris reduction

Clozel's trace formula in §5.1 of the 1991 paper gives powers of one
arithmetic Frobenius polynomial at each good place. The predicates here
describe such powers and the resulting systems of multiplicity one on the
automorphic base field. They use the same normalization at every place.
-/

noncomputable section

universe uE uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Global Langlands.Unramified

variable {E : Type uE} [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)]
variable {L : Type uL} [Field L] [NumberField L] {r : ℕ}

/-- A single common set of arithmetic characteristic polynomials, with the
specified power realized by actual representations. The polynomials before
taking powers have the rank and weight of the normalized cuspidal spectrum. -/
def HarrisPowerSystem (c : CuspidalOperatorRealization.IsoClass E r)
    (ι : L →+* ℂ) (excluded : Finset (FinitePlace L))
    (R : Collection.{uE, uL, uV} E L excluded) (a : ℕ) : Prop :=
  0 < a ∧ HasRank excluded R (a * (r + 1)) ∧
  ∃ (S : Finset (FinitePlace E)) (P : FinitePlace E → Polynomial L)
    (s : SpectralSystem (FinitePlace E) (r + 1)),
    CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uE, uW} c s ∧
    MatchesOutside excluded R S (fun v => ((P v) ^ a).reverse) ∧
    ∀ v ∉ S,
      (P v).Monic ∧ (P v).natDegree = r + 1 ∧ (P v).coeff 0 ≠ 0 ∧
      Cohomology.Weights.IsPurePolynomial (residueCardinality v) (r : ℤ) (P v) ∧
      ∃ hv : v ∉ s.exceptional,
        (P v).reverse.map ι =
          clozelEulerPolynomial (s.eigenvalues v hv) 1 (residueCardinality v)

/-- The same arithmetic normalization with each good-place polynomial
realized once. -/
abbrev HarrisNormalizedSystem (c : CuspidalOperatorRealization.IsoClass E r)
    (ι : L →+* ℂ) (excluded : Finset (FinitePlace L))
    (R : Collection.{uE, uL, uV} E L excluded) : Prop :=
  HarrisPowerSystem.{uE, uL, uV, uW} c ι excluded R 1

end Langlands.GaloisRepresentation
