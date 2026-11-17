# Canonical scheme residue fibres and Hopf centrality loci

This internal derived construction compares the ideal residue field used by
`HopfFiberCentrality` with Mathlib's canonical scheme-stalk residue field.
All statements work in an arbitrary common universe. The pullbacks are full
scheme pullbacks, and centrality is tested on every test scheme.

`isCentral_iff_of_iso_square` transports centrality through a commuting square
whose horizontal source and target comparisons are group isomorphisms. It uses
precomposition and postcomposition of central homomorphisms with those
isomorphisms and then cancels each isomorphism with its inverse.

`isCentral_baseChange_comp_iff` applies that transport to the natural
composition comparison for pullback functors on group objects.
`isCentral_idealResidue_iff_schemeResidue` factors the canonical map from the
scheme residue field through the spectrum of the ideal residue field via
`Scheme.Spec.residueFieldIso`. Centrality is preserved by this final pullback
and reflected because its base map is an isomorphism, hence flat and surjective.

`mem_fiberCentralityLocus_iff` specializes the comparison to the actual
Hopf-spectrum map. The provenance is derived from the canonical Mathlib residue
isomorphism, naturality of pullback composition, and the published all-test
centrality transport and fpqc reflection lemmas. No new structural theorem
about reductive groups is invoked.

`schemeFiberCentralityLocus` uses the canonical scheme residue fields directly.
Its equality with `fiberCentralityLocus` transfers both the inverse-image
identity under arbitrary scalar extension and constructibility over a
noetherian ring when both supplied Hopf algebras have finite type.

Under these noetherian and finite-type hypotheses, let `S` be a commutative
`R`-algebra and assume
`H : schemeFiberCentralityLocus (scalarExtensionMap S π) = Set.univ`.
Thus the actual scalar-extension Hopf-spectrum homomorphism is central on
every canonical scheme-residue fibre over `S`.
`schemeFiberCentralityCoefficientModel S π H t` chooses a finitely generated
`R`-subalgebra of `S` containing the finite set `t` and preserving this supplied
fibrewise centrality: the actual scalar-extension Hopf-spectrum map over the
coefficient ring is central on every canonical scheme-residue fibre.
Its coefficient ring is noetherian. The proof applies the existing ideal
residue coefficient construction to `H` and the comparison proved here;
the noetherian property follows from finite generation over a noetherian ring.
No noetherian assumption is imposed on `S`.

The construction starts from supplied Hopf algebras and a Hopf homomorphism.
It does not construct reductive group models or prove global centrality from
fibrewise centrality, so the host central-isogeny criterion remains open.
