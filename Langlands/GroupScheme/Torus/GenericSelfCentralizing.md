# Generic-fibre determination of a closed split-torus centralizer

This is an internal consequence of the published schematic-dominance,
split-torus centralizer, and maximal-torus theorems. It is a supporting input to
the generic-closure approach to reductive monomorphisms. It does not prove that
the ambient group has connected fibres or that the reductive monomorphism is
closed.

Let \(R\) be a commutative domain and \(K\) its fraction field. The lemma
`SubgroupFunctor.range_le_of_fractionField` says that a homomorphism from a flat
\(R\)-group \(A\) into a group \(G\) factors through a specified closed subgroup
\(D\) whenever the generic homomorphism does. The assertion is containment of
subgroup functors on all test schemes. The proof evaluates generic containment
at the identity map of \(A_K\), obtains a generic factorization, and descends
that factorization along the schematically dominant projection \(A_K\to A\).
Closedness of \(D\to G\) is essential to this descent.

Suppose \(G\) is smooth and affine over \(R\), and \(t:T\to G\) is a closed
split torus. If \(T_K\) is its whole centralizer in \(G_K\), then
`splitTorusCentralizer_eq_range_of_fractionField` proves that \(T\) is its whole
centralizer in \(G\), on every test scheme. The published split-torus theorem
supplies a smooth closed representative \(C\to G\) of the centralizer. In
particular \(C\) is flat. Centralizers commute with base change, so the generic
image of \(C\) lies in \(T_K\). The preceding flat-source lemma gives \(C\subseteq
T\) over \(R\). Commutativity of \(T\) gives the reverse containment.

`splitTorusCentralizerIsoOfFractionField` constructs the actual isomorphism
\(T\simeq C\) for any representative \(C\to G\) of this centralizer. Its
composition with the given centralizer inclusion is \(t\), as recorded by
`splitTorusCentralizerIsoOfFractionField_hom_comp` and its reassociated form.
No smoothness assumption is required on this independently supplied
representative: uniqueness of representatives identifies it with \(T\).

Finally, `splitTorusCentralizer_eq_range_of_genericMaximal` obtains the generic
self-centralizer hypothesis from the published theorem that a maximal torus
in a connected reductive group over a field equals its centralizer. It only
assumes reductivity and connectedness on the generic fibre. These conclusions
hold over any domain; no Dedekind, discrete valuation, or local-field hypothesis
is used. The closedness hypothesis on \(t\) remains explicit throughout.
