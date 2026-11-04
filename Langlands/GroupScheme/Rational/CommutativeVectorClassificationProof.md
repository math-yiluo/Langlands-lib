# Characteristic-zero commutative unipotent vector classification

Worker 1485. This internally assembled proof targets the unchanged proposition
`Langlands.GroupScheme.RelativeRoot.CommutativeUnipotentVectorCharZeroStatement`
at arbitrary universe `u`. Its hypotheses and conclusion are exactly those of
the published `CommutativeVectorClassificationStatement` module.

For a characteristic-zero field, `HasSplitSeries.isVectorGroupOfDimension_of_commutative`
proves by induction that a commutative affine group with a represented split
series of length `n` is a vector group of dimension `n`. The zero step uses the
existing all-test triviality and zero-dimensional coordinates. In a successor
step, the full closed kernel inherits affineness and commutativity, so induction
gives its vector coordinates. The quotient has one-dimensional natural vector
coordinates by the series definition. The polynomial correction construction
`CommutativeAdditiveExtension.exists_extensionSection` supplies an actual group
section of this flat surjective quotient. The natural split-extension product
coordinates then give dimension `n+1` on every scheme test.

For `commutativeUnipotentVectorCharZero`, the existing unconditional theorem
`Unipotent.algebraicallyClosedSplit` supplies the finite represented series from
smoothness, affineness, connectedness, and the Library's actual coefficient-
representation predicate `IsUnipotent`. Apply the preceding induction and forget
the chosen dimension. This reuses the published unipotence-to-series theorem;
no external unipotence comparison or additional classification premise is assumed.

The resulting `IsVectorGroup` consists of one finite dimension together with group
equivalences to that many additive global functions on every relative scheme
test, natural under every test morphism. It includes dimension zero and the
trivial group. The statement and its imported declarations are unchanged.
