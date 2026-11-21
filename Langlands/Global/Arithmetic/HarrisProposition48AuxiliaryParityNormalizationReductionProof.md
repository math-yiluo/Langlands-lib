# Auxiliary parity normalization from arithmetic and local transport

Author: Worker 998.

`Langlands.Global.Harris.proposition48AuxiliaryParityNormalizationReduction`
proves the unchanged Library proposition
`Langlands.Global.Harris.Proposition48AuxiliaryParityNormalizationReductionStatement.{uF}`.
It uses the four stated transport propositions as hypotheses. The number fields
are in `Type` as in `Proposition48Problem`; the local field universe `uF` is
arbitrary. No primary-place hypothesis is used.

## Implemented proof

1. Write `d = [E' : E] − 1` and `m = (b + d) % 2`. If `b % 2 = d % 2`,
   then `m = 0`; take the trivial Hecke character, with zero infinity type.
   Otherwise `m = 1`. Choose a complex embedding `τ` of the supplied imaginary
   quadratic subfield `K₀` and apply `HarrisDatum.halfWeights` to its inclusion
   into `E` (with the identity extension of `E`). The type is one on embeddings
   restricting to `τ` and zero on the others. `halfWeights_pure` uses the two
   conjugate embeddings of `K₀` to give pure weight one. Applying
   `cmHalfWeightCharacter` with the empty set gives a conjugate-inverse character
   `ν` on the actual idele classes. Its infinity formula is
   `IsAlgebraicAfterTwist 1 ν` by `pow_one`. This branch assumes no finite-place
   unramifiedness for `ν`.
2. Apply `NormTwistInfinityStatement` to `ξ` and `ν`. It supplies algebraicity
   of `ξ * (ν ∘ N_{E'/E})` after twist `b + m` and preserves relative
   regularity. A private lemma iterates `isAlgebraicAfterTwist_add_two_iff`
   by strong induction to compare each exponent with its residue modulo two.
   Since `(b + m) % 2 = d % 2`, the corrected character is algebraic after
   twist `d`. The `CMNormConjugationStatement` equation gives conjugate
   inversion of the norm pullback of `ν`; `HarrisDatum.isConjugateInverse_mul`
   then gives conjugate inversion of the corrected character.
3. At `Q.Ps`, `Proposition48PlaceNormTwistStatement` yields a corrected actual
   component and an ambient Weil character. The supplied character relation
   and the original general position hypothesis feed
   `GeneralPositionAmbientTwistStatement`. The remaining auxiliary validity
   clauses are unchanged by `withCharacters`: normalized reciprocity, the
   split imaginary quadratic field, the scalar tower and normal closure, the
   prime and compatibility conditions at `Q.Ps`, and uniqueness above that
   place and its conjugate. Together these give the corrected auxiliary datum.

## Provenance and scope

This is a derived implication for the induction in Harris, *The local
Langlands conjecture for GL(n) over a p-adic field, n < p* (1998), printed
p. 195 (the rank parity), Definition 4.5 and Proposition 4.8, pp. 201–203
(the auxiliary general-position place and induction). Registered source:
`harris-1998-local-langlands`, PDF pp. 19, 25–27. The choice of the trivial or
half-weight character uses the Library construction based on Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
Proposition VII.2.7 and the proof of Corollary VII.2.8, printed pp. 238–239,
244–245. Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`,
PDF pp. 246–247, 252–253. The formal proof does not prove the four transport
premises or Proposition 4.8 itself.
