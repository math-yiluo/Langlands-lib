# Actual split covers under direct and iterated scalar extension

This derived internal module constructs comparisons from a supplied spin cover
and a supplied orthogonal Morita comparison. Its provenance is the existing
identity-component base-change and isomorphism transport, base-change stability
of central isogenies, simple connectedness under field extension, and the actual
pullback-composition isomorphism and its naturality. It constructs no Morita
comparison, numbered root system or vector eigenbasis.

`splitCover` chooses the central isogeny whose existence is part of the supplied
`IsSpinCover`. It pulls that map back and composes it with the canonical
identity-component base-change isomorphism and the restriction of the supplied
Morita group isomorphism to identity components. The next theorems prove that
this is a central isogeny and that its source is simply connected.
`splitCover_factor` identifies its composite with the split orthogonal
identity-component inclusion with the scalar extension of the original cover
followed by the actual supplied Morita group isomorphism.

`splitCoverTower` gives the cover on the iterated scalar extension for a field
tower K to F to L, by precomposing `splitCover` with the canonical actual
iterated-to-direct pullback isomorphism. The tower is assumed compatible through
`IsScalarTower`. Centrality follows by isomorphism transport; simple
connectedness follows by applying field-extension preservation twice. The
factorization theorem uses naturality of that same pullback comparison and
retains its explicit component on the original isometry group.

`splitCoverTower_alignment` starts with a split pinning on the group extended
to F and full scheme-kernel fundamental-weight alignment for the original cover
extended to F. For an algebraic extension L/F, it proves alignment for the
actual scalar-extended pinning and `splitCoverTower`, retaining the original
simple vertex through `baseChangeSimpleEquiv`. The proof first applies the
published all-test-scheme alignment base-change theorem. Postcomposition with
the iterated-to-direct comparison and Morita isomorphism preserves the kernel.
The factorization equality then identifies this map with the constructed cover
followed by the identity-component inclusion. Removing that postcomposition
gives the required alignment. All tests remain arbitrary relative schemes;
there is no restriction on the characteristic or the cardinality of the fields.
