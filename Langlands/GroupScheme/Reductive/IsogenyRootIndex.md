# The actual root-index bijection of a split reductive isogeny

This internal derived unit proves that the source-to-target root-index map
chosen from finite actual source-root images is bijective for an isogeny
between connected reductive groups over an arbitrary field, with a commuting
map of specified split maximal tori and supplied actual root data.
The source root datum is assumed reduced.

`IsRootDatumOf.isogenyRootIndexEquiv` is oriented from source indices to target
indices. Its function is the target index chosen by `isogenyRootFactor`, so its
characteristic-power pullback equations are retained by
`isogenyRootIndexEquiv_spec`.

The implemented dimension argument decomposes the actual Lie module into the
zero torus weight and the weight lines indexed by the supplied roots. Actual
maximal-torus self-centralization identifies the zero weight with the intrinsic
tangent of the specified torus, and its monomorphic inclusion identifies that
tangent with its Lie module. The other summands have dimension one by the split
root Lie-line theorem. Thus the ambient Lie dimension equals the torus Lie
dimension plus the number of roots.

The isogeny and its actual torus restriction preserve smooth Lie dimensions,
even when their differentials are not injective. Subtracting the two dimension
identities gives equality of root counts. Reducedness gives injectivity of the
chosen index map: equality of target indices makes the source roots positively
proportional; reducedness identifies them up to sign, and the negative sign
contradicts positivity of the nonzero integer factors. Equal finite counts then
give bijectivity.

Provenance is derived from the published actual Lie weight decomposition,
maximal-torus centralizer theorem, split root Lie-line theorem, smooth-isogeny
dimension theorem, torus-restriction isogeny construction, and actual source-root
factor construction. This unit does not prove the coroot equations or the
centrality and isomorphism comparisons of `IsogenyRootDatumStatement`.
