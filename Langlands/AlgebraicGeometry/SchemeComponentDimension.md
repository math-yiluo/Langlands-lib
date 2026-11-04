# Dimension on opens of components of field schemes

This derived prerequisite supports the pure-dimensional fibre clause of
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2).
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The component comparison is internal rather than a separately numbered
assertion of the paper.

`OpenDimensionInvariant X` says that every nonempty open subspace of X
has the topological Krull dimension of X. `ComponentOpenDimensionInvariant X`
requires this property on each actual irreducible component of X with
its subspace topology. These are proposition definitions and do not
assume finite dimension, Noetherianity, or nonemptiness of X.

The two `of_homeomorph` results transport these conditions through actual
homeomorphisms, including between independent universes. They use open
preimages, the induced restricted homeomorphisms, and homeomorphism
invariance of topological Krull dimension. For components, the inverse
image of a component under a homeomorphism is a component.

`ComponentOpenDimensionInvariant.of_openCover` derives the component
condition from its validity on an arbitrary actual open cover.
For a component Z, restrict the cover to Z. Any member that meets a
nonempty open in this restricted cover yields a component of the original
chart. The actual intersection homeomorphism swaps the two subspace
orders, transporting the chart's open-dimension condition. The previously
proved open-cover criterion on the irreducible space Z gives the result.
Empty cover members are allowed, and the cover index has an independent
universe.

`componentOpenDimensionInvariant_spec_finiteType` proves the condition
for the spectrum of any finite-type algebra A over an arbitrary field k.
Each component is the zero locus of a minimal prime p. The nonempty-open
dimension comparison for that zero locus and the dimension of the
quotient spectrum identify both dimensions with that of A/p. The algebra
A need not itself be reduced or a domain, and k and A have independent
universes.

`componentOpenDimensionInvariant_affine` applies this result to the
actual global sections of an affine scheme X locally of finite type over
Spec k. The algebra structure comes from the given morphism f through
`affineStructureMap f`; its finite type is proved by
`affineStructureMap_finiteType`. The canonical isomorphism X ≅ Spec Γ(X)
transports the result.

`componentOpenDimensionInvariant_locallyOfFiniteType` proves the
condition for every scheme locally of finite type over Spec k.
The actual affine opens cover X, and each open has the composite
structure morphism to Spec k, which is locally of finite type. Apply
the affine comparison and the open-cover result. This imposes no
quasi-compactness, quasi-separatedness, or separatedness hypothesis.
The field and schemes lie in the common scheme universe.

These comparisons are proved prerequisites. Pure-dimension locality,
field-extension invariance, constructibility, and the full filtered
descent conclusion of Conrad's theorem remain separate obligations.
