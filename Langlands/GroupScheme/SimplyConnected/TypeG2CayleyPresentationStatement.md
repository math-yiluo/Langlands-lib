# Actual Cayley presentations of type-G2 groups

Author: Worker 177.

`Langlands.GroupScheme.TypeG2CayleyPresentationStatement` is an
unproved structural proposition over every field `K`, in every
characteristic. Its input is an actual affine, locally finite type,
simply connected, absolutely almost-simple group scheme `G` over
`Spec K`, actual Tits-index data `d`, and a numbering of all its simple
vertices by `Fin 2` that identifies every actual Cartan entry with
`CartanMatrix.G₂`. It has no local-field, split-rank, isotropy,
perfection or marked-vertex hypothesis.

Its conclusion supplies an actual `CayleyDatum K` and a morphism from
`G` to the actual group scheme `GL₈` satisfying
`c.IsAutomorphismRepresentation`. The datum contains an actual unital
bilinear multiplication and nonsingular multiplicative quadratic norm
on `K⁸`. The representation is a closed immersion, and its range on
every test scheme is exactly the invertible matrices fixing the identity
and preserving multiplication after coefficient extension. Nonreduced
tests are included. A comparison of rational points alone does not
establish this conclusion.

The source is Knus, Merkurjev, Rost and Tignol, *The Book of
Involutions*, Theorem 26.19, printed p.373 / PDF p.396. It states an
equivalence between Cayley algebras and simple algebraic groups of type
G2 over an arbitrary field. Its proof descends the multiplication
tensor, using the innerness of type-G2 automorphisms. Theorem 25.14,
printed p.360 / PDF p.383, identifies the split model as both simply
connected and adjoint. Theorem 33.17, printed pp.459–460 / PDF
pp.482–483, identifies eight-dimensional unital composition algebras
with Cayley algebras. The proposition here is a derived coordinate and
scheme-level presentation of that source result. Its proof must
construct the Cayley multiplication and norm from the actual type-G2
group, choose coordinates, and prove the actual closed-immersion and
all-test range comparison. This module supplies none of those
constructions.

The module also proves the following conditional local consequences:

- `CayleyDatum.exists_nonzero_norm_eq_zero` applies to any Cayley datum
  over a nonarchimedean local field. If its norm were anisotropic, the
  published theorem `Langlands.localQuadraticAnisotropicDimensionBound`
  would bound the dimension of `K⁸` by four. Its actual dimension is
  eight, a contradiction. Mathlib's
  `QuadraticMap.not_anisotropic_iff_exists` supplies the nonzero vector
  with zero norm. This lemma uses no group-structure premise, and
  includes every field and residue characteristic.
- `localTypeG2_splitRank_eq_two_of_cayleyStructure` assumes both the
  general presentation proposition above and the separate unproved
  `IsotropicCayleyAutomorphismRankStatement`. The presentation supplies
  the datum and its actual representation; the preceding lemma gives
  norm isotropy; the second premise gives `splitRank G = 2`.
- `localRankOneTypeG2_false_of_cayleyStructure` adds `splitRank G = 1`
  and contradicts that equality.
- `localRankOne_not_hasG2Index_of_cayleyStructure` extracts the full
  type-G2 Cartan comparison from the existing actual-index predicate
  `d.HasRankOneG2Index` and applies the contradiction. The exact
  long-root singleton marking and trivial full star action remain part
  of that predicate; they are not needed by the stronger type-G2 rank
  argument.

The general isotropic automorphism rank premise has its own paired
source explanation in
`Langlands/GroupScheme/Composition/IsotropicCayleyAutomorphismRankStatement.md`.
It retains the algebra classification, split-model and actual
split-rank comparison obligations. The conditional arguments here use
the already proved local quadratic dimension bound and elementary
dimension and rank arithmetic; they do not prove either structural
premise. No downstream local rank-one classification or local
Kneser–Tits theorem is used. The exact local index enumeration remains
unproved.

The retained official author errata and relevant page-sorted unofficial
comments were checked. The flagged reference in the proof of
Proposition 33.6 is not used.
