# Schur and determinant helpers for scalar-twist reduction

These derived helpers support the proof of
`Langlands.Weil.UnramifiedReduction` in the companion
[reduction module](UnramifiedReductionProof.md). The main proof constructs
the scalar-twist witness used here. The group and carrier universes
remain independent.

`scalar_of_commuting_unit` bundles an invertible operator commuting with
the representation into a self-intertwining map. Mathlib's
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`
then expresses it as a complex scalar. Genuine irreducibility makes the
group-algebra module, and hence the underlying vector space, nontrivial.
The unit cannot be zero in its endomorphism ring, so its scalar is nonzero
and defines an element of `ℂˣ`. This is the Schur-lemma step used to pass
from the general commuting correction to the irreducible scalar correction
in the cited reduction; it needs no topology.

`determinant_order_of_finite_range` lifts the representation to its genuine
unit-valued group homomorphism. Its range is finite because forgetting the
units is injective. The exponent of this finite group is positive and
annihilates every element. Applying the determinant gives one common
positive exponent for all determinant values. This direction allows zero
dimension and does not require irreducibility. Its helper also works without
finite dimension, using Mathlib's determinant convention in that case.

`finite_range_character_of_pow_eq_one` includes the character image in the
group of roots of unity of a fixed positive order. Mathlib proves this
group finite over a domain. `finrank_pos_of_irreducible` uses the actual
irreducibility predicate to give a simple group-algebra module, hence a
nontrivial vector space and positive finite dimension.

`finite_range_character_of_twist_determinant` applies the published
`Langlands.det_twist`. If the determinant of the twist has exponent `n`,
the finite-image representation's determinant has exponent `m`, and the
dimension is `r > 0`, raising the determinant identity to these exponents
gives `chi(g)^(r*n*m) = 1`. The common exponent is positive, so the preceding
root-of-unity argument applies.

`finite_range_iff_determinant_order_of_scalar_twist` combines these facts.
Its scalar-twist witness is explicit: the main unramified-reduction proof
must supply it without extra hypotheses. Once the character and the
untwisted representation both have finite image, the published
`OperationClosure.finite_range_twist` proves finiteness of the twist.

This is the derived determinant argument described in `Structure.md`, not
a separately numbered assertion in the original literature. The surrounding
reduction is Henniart 1980, sections 2.3-2.6, printed pages 158-160 (PDF 5-7),
and Tate 1979, section 2.2.1, printed page 10 (PDF 19). Worker 66 read those
original passages and Tate's determinant convention on printed page 9
(PDF 18); their retained file hashes agree with the target's citations.
The proof here is elementary algebra using the existing twist formula,
finite group exponents, simple-module nontriviality and finite roots of unity.

Worker 66 developed this helper module as part of the joint proof.
