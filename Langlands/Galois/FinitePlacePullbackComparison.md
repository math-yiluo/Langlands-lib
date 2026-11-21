# Compatibility of Galois pullback with finite-place restriction

For an extension \(E/K\) of number fields and a finite place \(w\) of \(E\)
above \(v\) of \(K\), `FinitePlacePullbackComparisonStatement` compares two
actions of \(\operatorname{Gal}(\overline{E_w}/E_w)\) obtained from an actual
finite-dimensional continuous representation of
\(\operatorname{Gal}(\overline{K}/K)\). The first pulls back from \(K\) to \(E\)
and restricts at \(w\). The second restricts at \(v\) and pulls back along
the completion embedding \(K_v\to E_w\). The conclusion supplies an
invertible linear intertwiner over the original coefficient field.

For successive field embeddings, `pullbackCompEquiv` composes their chosen
embeddings of algebraic closures. Uniqueness of restriction along this
composite identifies it with the two successive group restrictions. The
Library's `pullbackAlongClosureEquiv` changes from the composite closure
embedding to the chosen embedding for the composite field map.
`atFinitePlacePullbackEquiv` applies this construction on both sides of
the commuting square of number fields and their completions.

This is an internal consequence of the Library's closure restriction and
completion embedding constructions. It supplies the comparison of actual
Galois actions when the auxiliary extension in Harris (1999), Theorem
5.9(ii), splits at \(v\).
