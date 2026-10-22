# Isogenies of bundled abelian schemes

`Langlands.AbelianScheme.IsIsogeny f` restricts the published
`GroupScheme.IsIsogeny` predicate to the actual homomorphism of group
schemes underlying a morphism between bundled `AbelianScheme` objects.
The bundle includes explicit commutativity, smoothness, properness, and
geometrically connected fibres, as specified in `Basic`.

`isIsogeny_iff` identifies this predicate with the conjunction that the
underlying scheme morphism `hom f` is finite, flat, and surjective. The
equivalence is definitional. No alternative characterization of isogenies
is asserted.

`isIsogeny_id`, `IsIsogeny.comp`, and `IsIsogeny.baseChange` specialize the
published group-scheme stability theorems. The identity, composite, and
base-changed abelian-scheme homomorphisms have definitionally the same
underlying group-scheme morphisms as in those theorems. The base-change
map is the actual pullback map supplied by `AbelianScheme.baseChange`.
The schemes `S` and `T`, and the morphism `T → S`, are arbitrary.

This is an internal interface specialization of the published `Basic`,
`Isogeny`, and `IsogenyStability` modules. It adds no new literature claim,
no new geometric proof obligation, and no rational-invertibility
assumption. The proofs directly apply the existing generic stability
lemmas; the chosen general-base finite-flat-surjective convention and
its literature provenance remain those documented in `Isogeny.md`.
