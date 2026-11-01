# The actual induction–Jacquet identity for a one-block shape

Author: Worker 194.

This module derives an actual representation equivalence and its exact
finite-length Grothendieck-group consequence directly from the published
normalized functors. The principal result
`Langlands.Aubert.inductionJacquetK0_of_length_eq_one F T B hB` states that
`normalizedInductionK0 F T B` composed with `normalizedJacquetK0 F T B`
is `LinearMap.id` when `B.length = 1`. It is an internal consequence of the
actual quotient, Levi and induction constructions, with no additional
classification or representation-theoretic hypothesis.

The actual radical is trivial by
`BlockShape.subsingleton_unipotentRadical`. The internal
`trivialCoinvariantEquiv` descends the identity linear map through the actual
coinvariant quotient and uses the quotient map as its inverse. The
coinvariant relations vanish because every radical element is the identity.
`singleBlockJacquetEquiv` checks the normalized Levi action on representatives.
The explicit full block modulus is one by `singleBlock_leviModulus`, so its
inverse square root is one. Transporting along the inverse of the actual
`singleBlockLeviEquiv` cancels its embedding. The equivalence therefore
recovers the original ambient representation, and its `_mk` lemma sends the
quotient class of any vector to that vector.

`inductionJacquetSingleBlockEquiv` composes this with the published
`singleBlockNormalizedInducedEquiv`. That equivalence evaluates at the identity
and identifies the actual normalized induction action, defined by right
translation and positive half-modulus covariance, with the action transported
along the inverse of the single-block Levi equivalence. Thus the composite
equivalence is between the actual induction-after-Jacquet object and its
original input.

The K0 proof applies `FiniteLengthGrothendieckGroup.hom_ext_object` and the
published generator formulas for both exact maps. The actual representation
equivalence identifies their output class with the original class. This
proves equality on all virtual classes of the exact finite-length smooth
Grothendieck group, retaining all short exact sequence relations, including
nonsplit ones. Field universe `uF` and carrier universe `uV` are independent;
the K0 result uses saturated carriers in `Type (max uF uV)`. The representation
equivalences themselves allow arbitrary carrier universe `uV`.

The corollary `inductionJacquetK0_of_cuts_eq_empty` uses the published equality
`B.cuts.card = B.length - 1`, together with positive rank, to obtain
`B.length = 1`. The statement does not treat rank zero, whose unique empty
shape has length zero and is handled by the separate rank-zero construction.
No involutivity or induction-commutation theorem is assumed or proved here.
The import closure contains no analytic segment classification,
multisegment exhaustion, ordered strong-head existence, quotient coverage,
tempered block uniqueness, square-integrable classification or exhaustion,
regular exhaustion, or irreducible-image theorem.
