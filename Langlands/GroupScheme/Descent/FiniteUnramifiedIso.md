# Specified isomorphisms at finite unramified Galois stages

This internal construction combines finite-stage descent of actual group-scheme
isomorphisms with finite unramified field factorization. It is an input to the
integral-model descent proof, and does not itself construct an integral model or
prove effective descent.

Let `F` be a nonarchimedean local field in an arbitrary universe `u`. Let `E` be a
finite-dimensional intermediate field of the chosen `SeparableClosure F`, with
`hE : E ≤ inertiaFixedField F`. For group schemes `G` and `H` over `Spec E`, assume
the structure morphism of `G` is quasi-compact and quasi-separated, and that of
`H` is locally of finite presentation. Start with a specified group-scheme
isomorphism `e` after the actual inclusion `E → inertiaFixedField F`.

`fieldSpecMap` is the spectrum map of the inclusion of two intermediate fields.
`fieldSpecMap_comp` identifies the composite with the map of the composite
inclusion.

`IsoStage F E hE e` records an actual intermediate field `E'` of the same
separable closure, finite-dimensional and Galois over `F`, containing `E`, and
contained in the inertia fixed field. It also records the published predicate
`ArithmeticUnramified F E'`, a group-scheme isomorphism over `E'`, and an equality
identifying its pullback with the supplied `e`. The pullback uses `pullIso` and
the actual inclusion spectrum maps; the equality retains the canonical
direct-versus-iterated pullback comparisons. Galoisness of the original `E` is
not assumed.

`nonempty_isoStage` proves existence of this package and `isoStage` chooses one.
The implemented proof first installs the algebra structure on the inertia fixed
field from the specified inclusion of `E`. Algebraicity over `F` implies
algebraicity over `E`, so `FiniteStage.isoModel` descends the supplied isomorphism
to a finite intermediate field `K/E` with its recovery equation. Finite
dimensionality is transitive, giving a finite-dimensional `F`-field `K` with a
specified embedding into the inertia fixed field.

`fieldFactorization` then factors that embedding through a finite Galois
arithmetically unramified `E'/F`. Its exact factorization equality shows that `E'`
contains `E`, that the actual inclusion of `E` agrees with the map through `K`,
and that the composite `K → E' → inertiaFixedField F` is the original embedding.
Pulling the finite-stage isomorphism to `E'` gives the output.

Private coherence lemmas supply the final recovery equality. `pullHom_projection`
identifies the underlying scheme projection after pulling a morphism back.
The composite of two `intermediateProjection` maps is the projection of the
composite base map. Pullback extensionality then proves that successive `pullHom`
and `pullIso` operations equal the operation for the composite. A separate
comparison lemma identifies `FiniteStage.comparison` with the inverse of
`pullbackComparison` using their actual projections. The original finite-stage
recovery equation and these identities prove the equality in `IsoStage`.

The provenance is internal: the mathematical inputs are the finite-stage
isomorphism construction and the finite unramified field-factorization
construction imported by Lean name. No new assertion of model descent,
semilinear compatibility, or an extension theorem is assumed or proved here.
