# Nilpotent centrality with a multiplicative-type source and affine target

This is an internal consequence of the actual diagonalizable centrality
theorem and flat descent. It adds no assertion attributed to external
literature.

Let \(R\) be an arbitrary commutative ring, \(I\subseteq R\) a nilpotent
ideal, and \(i:H\to G\) a homomorphism of group schemes over
\(\operatorname{Spec}R\). Assume that the total scheme of \(G\) is affine
and that \(H\) is of multiplicative type in the relative Library sense:
an fppf cover makes it diagonalizable with finitely generated character
groups. If the actual base change of \(i\) to
\(\operatorname{Spec}(R/I)\) is central, then \(i\) is central. Centrality
means the existing `IsCentral` predicate, with every test scheme and every
restriction. No monomorphism, flatness, smoothness or finite-presentation
assumption on \(i\) or \(G\) is used in this conclusion.

`IsCentral.of_flatCover` is a more general helper over any scheme \(S\):
centrality is detected by a jointly surjective family of flat maps to
\(S\). For each test scheme, pull back that family. The multiplicative
base-change point equivalence turns centrality of each pullback into the
desired commutation equation on each member of the pulled-back family.
The private `hom_ext_flatCover` proves that these equations imply equality
of the original scheme morphisms: the map from the disjoint union of the
family is flat and surjective, hence an epimorphism. Flatness follows
from its local-on-source property; the covering condition gives
surjectivity. No quasi-compactness assumption is needed.

The remaining declarations lie in
`Langlands.GroupScheme.MultiplicativeTypeAffineInfinitesimalCentrality`.

`isCentral_baseChange_comp_iff` compares centrality after direct and
successive base changes. The naturality of
`Descent.pullbackComparison` identifies the two maps after source and
target isomorphisms. Precomposition preserves centrality and target
isomorphisms preserve it in both directions. Its consequence
`isCentral_baseChange_of_commSq` carries centrality through any commuting
base square, expressing its conclusion as a successive base change.

For an \(R\)-algebra \(B\), write \(J=IB\).
`isCentral_quotient_baseChange` applies this square comparison to
\[
\begin{array}{ccc}
\operatorname{Spec}(B/J)&\longrightarrow&\operatorname{Spec}(R/I)\\
\downarrow&&\downarrow\\
\operatorname{Spec}B&\longrightarrow&\operatorname{Spec}R.
\end{array}
\]
The top map comes from `Ideal.quotientMap`; it factors the scalar map
through both quotients. This lemma needs no nilpotence hypothesis.
`isNilpotent_map` proves nilpotence of \(J\) from that of \(I\), using
preservation of ideal powers and zero under ideal extension.

`isCentral_baseChange_of_isDiagonalizable` applies the affine
diagonalizable theorem to the base change along
\(\operatorname{Spec}B\to\operatorname{Spec}R\), provided the pulled-back
source is diagonalizable. The quotient-square lemma supplies its reduced
centrality hypothesis. The target remains affine because it is the
pullback of an affine morphism to an affine scheme.
`isCentral_affineChart_of_isDiagonalizable` gives the same conclusion for
any scheme morphism between the two spectra: its ring homomorphism
supplies the algebra structure, and `Spec.map_preimage` identifies the
resulting algebra base map with the given morphism.

`isCentral_of_isMultiplicativeType` chooses an fppf splitting cover of
\(H\) and then an affine open cover of each splitting scheme.
Diagonalizability persists on the affine charts; the direct/successive
pullback comparison supplies the required presentation of the source on
each chart. The preceding affine-chart theorem proves centrality there.
Two applications of `IsCentral.of_flatCover`, first to the affine open
cover and then to the fppf cover, prove centrality of the original map.
The argument does not require the splitting schemes themselves to be
affine.

`commGroupSchemeOfNilpotentQuotient` adds the explicit hypothesis
`Mono i.hom.hom`. It applies the preceding theorem and the existing
`IsCentral.commGroupScheme` construction to equip the original source
with commutativity. The accompanying `_toGrp` theorem is reflexive
equality of its entire underlying group scheme with \(H\), so its scheme
and group operations are retained.

The base in this result is affine, the thickening is a quotient by a
nilpotent ideal, and the target total scheme is affine. This does not
prove the published infinitesimal-centrality statement for arbitrary
locally nilpotent closed immersions and nonaffine targets. It also does
not lift multiplicative type from the special fibre or prove the full
fibrewise central-isogeny criterion.
