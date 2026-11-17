# Source changes and joins through coefficient extension

This internal coherence unit derives compatibility of actual source changes and
specified comparison joins with coefficient extension from the original atlas
transition cocycle. Its maps are complete order-linear formal maps.

For two refinements `q` and `r` of one atlas with equal finer covers,
`CoverRefinement.orderSourceIso_baseChange` compares the two routes from the
extension of `q`'s restricted order action to `r`'s restriction of the extended
order action. One route first uses `q.orderBaseChangeIso`, then the extended
refinements' actual source-change map. The other extends the original
source-change map, then uses `r.orderBaseChangeIso`.

The proof reduces the equality to complete formal coordinate maps. Each route
is a composite of two transitions between selected original charts. The two
atlas cocycles reduce these to single transitions, and `baseSource_sourceChart`
identifies their first original sources. The selected sources after extension
remain separate; coefficient maps need not be injective.

The parameters are arbitrary commutative rings `O` and `R` with an `O`-algebra
structure, a ring `D` over `O`, a finite coordinate type, an actual full-order
atlas action, two refinements with equal finer covers, and any commutative
`R`-algebra. Finer covers need not be finite.

`OrderAction.Iso.baseChange_trans` derives compatibility of coefficient
extension with composition of complete formal isomorphisms from the existing
homomorphism composition theorem and whole-isomorphism extensionality.

`OrderAction.Comparison.baseChange_join` proves an exact equality of comparison
records. The outer refinements on both sides are the same. After passing to
the forward formal maps and preserving their compositions under extension,
the source-change square identifies the two middle correction routes.
Associativity and the actual inverse equations cancel the middle correction
isomorphism. Extensionality determines the whole isomorphism, including its
inverse. No equality of independently selected original charts is assumed,
and equality of point evaluations is not used to detect formal-map equality.
