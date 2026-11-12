# Algebraically closed field tests for connected fibres

This internal supporting module proves that the published predicate
`HasGeometricallyConnectedFibres` can be tested on algebraically closed
fields. All schemes and fields remain in the arbitrary universe `u`.
Neither finiteness nor representability of the algebraic-space morphism
is assumed. Nonemptiness remains part of every `ConnectedSpace` conclusion.

For a presheaf morphism `f : F → G`, a scheme-test map `k : U → V` over
`S`, and `y : h_V → G`, `fibreSchemeTestMap` is the actual morphism from
`F ×_G h_U` (using `h_k ≫ y`) to `F ×_G h_V`. It is defined by the first
pullback projection and the second projection followed by `h_k`. Its two
projection identities are proved. Cancelling the original fibre's
cartesian square from the composite square proves that this fibre map is
itself the pullback of `h_k`. Consequently, if the underlying scheme map
`k.left` is surjective, the represented fibre transformation is
geometrically surjective by the existing relative-property base-change
lemma and the scheme-Yoneda surjectivity result.

`fibreSchemeTestMap_continuous` proves continuity of the induced point
map when `f` is the presheaf map of an algebraic-space morphism. The actual
algebraic-space fibre product supplies a surjective étale atlas of the
target fibre, transported through its whole-presheaf isomorphism. The
general target-atlas continuity criterion in `SpaceMorphismPointMap`
applies. This does not require the fibre transformation itself to be étale.

For two field tests and any morphism between them, the underlying scheme
map is surjective: its domain is nonempty and its target is a singleton.
The relative-surjectivity result therefore makes the actual fibre point
map surjective. Its continuity and surjectivity show that connectedness
of the extended fibre implies connectedness of the original fibre. This
is `connectedSpace_fibre_of_field_extension`; it includes nonemptiness
through the continuous-surjective image theorem for connected spaces.

The forward implication of
`hasGeometricallyConnectedFibres_iff_algClosed` restricts the original
universal field tests. For its converse, extend an arbitrary field `K` to
`AlgebraicClosure K`, compose the structure map to `S`, and pull the target
section back along the actual represented scheme map. The hypothesis on
algebraically closed field tests gives connectedness of this extended
fibre. The preceding field-extension result descends it to the original
fibre over `K`.

The provenance is internal: these are actual pullback constructions and
composite proofs from scheme-Yoneda relative surjectivity, point-map
continuity and surjectivity, and the algebraic closure of a field. No
external theorem or additional descent premise is assumed. This unit is
infrastructure for the remaining connected-fibre clause; it does not prove
eventual limit descent or complete `SpaceLimitPropertyDescentStatement`.
