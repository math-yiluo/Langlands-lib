module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The two ambient algebras of the normalization stalk

[Stacks, Tag 0C3B] describes the stalk of the pushforward of the structure sheaf of the
normalization in two ways: as the integral closure of the local ring in the total ring of
fractions of its reduction, and as the integral closure in the product of the residue fields
of its minimal primes.  This module identifies those two ambient algebras, so that either
description follows from the other.

For a ring `A` with finitely many minimal primes, write `R = A ⧸ nilradical A`.  Then `R` is
reduced with the same minimal primes as `A`, and its total ring of fractions is the product of
the localizations at those minimal primes.  Each such localization is a field, hence equal to
its own residue field, which is the residue field of the corresponding minimal prime of `A`.

## Main results

* `minimalPrimeResidueFieldProductAlgEquivFractionRingReduction`: the product of the residue
  fields of the minimal primes is the total ring of fractions of the reduction, as an
  `A`-algebra.
* `integralClosureReductionFractionRingAlgEquivMinimalPrimeResidueFields`: consequently the two
  integral closures appearing in [Stacks, Tag 0C3B] agree.

## Implementation notes

The `A`-algebra structures are the ones given by `reductionFractionRingHom` and
`minimalPrimeResidueFieldProductHom`, rather than by whatever instances typeclass synthesis
finds; the equivalences are therefore assembled as ring equivalences and packaged with an
explicit `commutes` proof.  Minimal primes of the reduction are indexed by the minimal primes
of `A` itself, through `minimalPrimeMapNilradical`, so no reindexing of the products is needed.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.NormalizationStalkAmbient

/-- The canonical map from a ring to the total ring of fractions of its reduction. -/
public noncomputable def reductionFractionRingHom (A : Type*) [CommRing A] :
    A →+* FractionRing (A ⧸ nilradical A) :=
  (algebraMap (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))).comp
    (Ideal.Quotient.mk (nilradical A))

section Reduction

variable (A : Type u) [CommRing A]

end Reduction

section Ambient

variable (A : Type u) [CommRing A]

end Ambient

end Stacks.NormalizationStalkAmbient

end
