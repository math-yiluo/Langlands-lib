# Induced maps and changes of exceptional set

This module implements the induced-map construction in Flath (1979), §2,
printed p.181, numbered (1), using the actual finite stages and direct limit
from `RestrictedTensor.Basic`. Source `flath-1979-tensor-products`, retained
Corvallis Part I PDF SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`,
one-based PDF p.177.

The coefficient field `K`, index type, and source, intermediate and target
carrier families have independent universes. Each carrier has only an
additive commutative group and a `K`-module structure. No finite dimension,
topology, injectivity or surjectivity of a component map is required.
The construction works on the generalized direct limits `Space K V E e`;
it therefore specializes directly to `Product K V E r`, where `r` contains
the prescribed nonzero reference vectors outside `E`.

## Constructed map

For finite exceptional sets `E,E'`, total reference families `e,e'`, and
component linear maps `f_i : V_i → W_i`, assume
`f_i(e_i) = e'_i` for all but finitely many indices. A finite set `F`
contains the target exceptional set and every failure of this equality.
`mapStage` enlarges a source stage `S` to `S ∪ F`, applies the component
linear maps at that stage, and maps the result into the target limit.

`mapStage_transition` proves compatibility with source transition maps.
It checks elementary tensors at a common larger stage: coordinates already
in the smaller stage are retained, while every newly adjoined coordinate
outside `F` uses the stated reference-preservation equality.
`mapWithBound` then descends this compatible family through the actual
direct-limit universal map.

`hom_ext_cofinal` proves that a linear map out of the limit is determined
by elementary tensors on stages containing any prescribed finite set.
Applying it to the union of two bounds proves `mapWithBound_eq`.
Thus the chosen bound is immaterial.

`mapBound` obtains a finite bound from the cofinite preservation hypothesis.
`map` uses this bound; `map_eq_mapWithBound` permits any other adequate
one. The formulas `map_pure`, `map_pure_of_subset`, and
`map_pure_of_preserves` respectively describe enlargement by the chosen
bound, evaluation on a stage containing that bound, and evaluation on
any stage outside which the maps preserve the references. The last formula
does not require the internally selected bound to lie in that stage.

## Functoriality and equivalences

`preserves_comp` proves that componentwise composition preserves the references
cofinitely. `map_comp` proves that its induced map is the composite of the
induced maps, even when all three exceptional sets differ. The proof uses
cofinal extensionality with the union of the three relevant finite bounds.
`map_id` proves the identity law. Preservation proofs themselves do not affect
the maps, by Lean proof irrelevance.

For a family of component linear equivalences, `preserves_symm` proves the
reverse preservation condition and `congr` constructs a genuine linear
equivalence of the restricted tensor spaces. Its two inverse identities
follow from `map_comp`, the local inverse identities, and `map_id`.

`change` is the identity-component equivalence for any two finite exceptional
sets and reference families equal cofinitely. It changes no tensor coordinate
on a stage containing the finite exceptional data. `change_refl` and
`change_trans` prove identity and successive-change coherence.
`change_natural` proves compatibility of these equivalences with induced
component maps whenever both corresponding cofinite preservation conditions
hold.

`ReferenceVectors.restrict` restricts the prescribed nonzero-vector data when
the exceptional set is enlarged. The resulting total reference families agree
outside the larger exceptional set. `changeExceptional` supplies the induced
equivalence between the two actual `Product` carriers.

## Provenance and scope

The induced-map construction is the explicit implementation of Flath's
section 2, numbered (1). The finite-bound independence, universal-map
arguments, identity/composition laws, component equivalences and coherence
are intrinsic algebraic proofs of this construction. They use the actual
finite stages and limit from `Langlands.Representation.RestrictedTensor.Basic`
and the pinned Mathlib cofinite-filter and linear-map APIs. No maps or their
laws are postulated as fields.

Full-limit finite-factor separation is a separate construction. Group
actions and smoothness are implemented in the associated `Action` and
`Smooth` modules. This module asserts no factorization of automorphic
representations, admissibility or completed tensor product.
