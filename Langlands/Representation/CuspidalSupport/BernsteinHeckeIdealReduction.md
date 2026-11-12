# The Bernstein Hecke-ideal assertions from actual decomposition

This is a derived reduction of Renard (9 July 2026), VI.7.4,
printed pp.185–186 / PDF pp.191–192. It proves the exact published
`BernsteinHeckeIdealDecompositionStatement` conditionally on the exact published
`BernsteinDecompositionStatement` in its required carrier universe
`max uF uV`. It preserves the actual standard families, cuspidal data, inertial
classes, full block properties, regular representation and Haar Hecke algebra.

Given central operators with the stipulated identity and zero actions on the
actual blocks, uniqueness of the central projectors of the supplied decomposition
identifies them with the canonical projectors. They are therefore idempotent,
orthogonal and have vectorwise finite reconstruction. Their fixed Hecke ideals
are their exact images on the lifted regular representation and are two-sided
ideals. The canonical additive direct-sum map is bijective by
`decomposition_centralIdeals_isInternal`.

The actual Bernstein block property is stable under smooth isomorphisms.
`decompositionIdealEquivalence` consequently identifies each block with the
nondegenerate modules over its central Hecke ideal. Its exact natural comparison
with the ambient inclusion, integrated Hecke functor and scalar restriction is
the comparison required by the published target.

`bernsteinCentralIdempotentStatements_of_decomposition` combines this reduction
with the previously published first-conjunct reduction. Its two premises are the
actual decomposition target at carrier universes `uV` and `max uF uV`,
respectively; they need not be inferred from each other. No hypothesis of the
published targets is added or conclusion weakened: these are explicit
conditional helper theorems, and the unconditional decomposition premises remain
separate proof obligations.
