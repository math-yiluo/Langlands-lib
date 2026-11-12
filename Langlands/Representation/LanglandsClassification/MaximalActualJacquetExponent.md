# Maximal selection among actual normalized Jacquet exponents

Worker 148. This internal construction uses the published theorem
`arbitraryParabolicExponent` (Renard VII.1.1) to provide the finite, nonempty
actual exponent family needed for the maximal-norm choice in VII.4.2(iii).
It does not prove Langlands exhaustion.

For an admissible smooth representation of the rational points of a connected
reductive group over a nonarchimedean local field,
`normalizedJacquetExponents_nonempty_iff` identifies nonemptiness of the
published normalized exponent set with nontriviality of its actual normalized
Jacquet module. One direction uses the nonzero weight space of an exponent.
In the other direction, VII.1.1 says the weight submodules span the module.
An empty exponent set would have supremum bottom, contradicting top being
different from bottom in a nontrivial module.

The field has the published valuation, topology, local-field and Hausdorff
instances. The ambient group has an affine structure morphism, supplied by
connected reductivity in applications. Its rational points carry the canonical
point topology, with local-compactness and nonarchimedean-group instances.
These are the same ambient conventions as the published exponent theorem.

For a supplied family `D` of actual `ParabolicDatum G` with supplied split
components `A`, `a`, `ha`, `taggedActualJacquetExponents` is the dependent sum
of their actual exponent subtypes. Its members retain the original label and
the character on that label's split component. No identification of characters
on different split components is made.

`finite_taggedActualJacquetExponents` uses VII.1.1's finite-support conclusion
at every label. Admissibility and finite length of the original representation,
together with finiteness of the label type, suffice. It does not require a
separate finite-length preservation result for Jacquet restriction.
`nonempty_taggedActualJacquetExponents_iff` says this family is nonempty exactly
when one supplied Jacquet module is nontrivial.

For any supplied map `positive` from these tagged exponents to a normed additive
commutative group, `maximalActualJacquetExponent` chooses a member maximizing
its norm. It applies the finite-family selector `maximalPositiveProjectionIndex`
to the finite universal set. `norm_le_maximalActualJacquetExponent` proves the
bound for every tagged exponent. The field, representation carrier, label type,
and normed group have independent universes.

The provenance is an internal consequence of the published actual VII.1.1
decomposition and finiteness theorem and the elementary finite-maximum
construction. The motivating source is David Renard, *Représentations des
groupes réductifs p-adiques*, 9 July 2026 edition, VII.1.1, printed pp.220–221 /
PDF pp.226–227, and VII.4.2(iii), printed pp.243–244 / PDF pp.249–250,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This unit assumes the finite family of parabolics, their split components,
admissibility, and the map called `positive`. It constructs none of the full
real-character lifts, central complement, positive-part decompositions, cone
comparisons, or Langlands triplet. Admissibility is retained explicitly, even
when the intended representation is irreducible. These obligations and the
temperedness and quotient arguments remain necessary for the classification.
