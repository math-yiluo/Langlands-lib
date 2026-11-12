# Generic constancy of actual geometric fibre components

This is an internal supporting construction for the geometric fibre component
constructibility problem. It combines the existing finite etale splitting,
split-generic constancy and actual geometric-fibre transport results. It does
not assert constructibility over arbitrary rings.

`openBaseChangeAtlasIso` compares the actual chart formed by restricting an
atlas scheme to an open `V` and pulling it back along `g : T → V` with the
chart obtained by base change along the composite `g ≫ V.ι`. It pastes the
open-restriction pullback square with the second pullback square and takes
the resulting isomorphism over `T`.

`openBaseChangeAtlasMap` applies the relative Yoneda functor to this isomorphism
and composes with the ordinary restricted atlas. Its source is exactly the
scheme used by finite etale generic component splitting. The two following
lemmas show that this atlas retains etaleness and geometric surjectivity,
using the corresponding properties of the ordinary restricted atlas and
invariance under isomorphisms. These constructions work for arbitrary base
schemes and arbitrary presheaves with the stated atlas property.

`exists_open_geometricComponentsEquiv` assumes an irreducible Noetherian base,
a quasi-separated algebraic space and an etale surjective atlas whose
structural scheme morphism is locally of finite type and quasi-compact. It
constructs a nonempty open subset on which the actual geometric fibre
component sets are pairwise equivalent. Both endpoints use the published
quotient point space and its `pointTopology`. No generic splitting premise
is retained in this theorem.

The proof applies `finiteTypeFiniteEtaleGenericComponentSplitting` to the
atlas structure map. This supplies a finite etale cover of a nonempty open,
with irreducible affine source and geometrically irreducible generic chart
components. The source is Noetherian by local finite type over the open
Noetherian base and compactness of affine schemes. The explicitly constructed
atlas has the exact structure morphism in the splitting conclusion; its
local finite type and quasi-compactness follow by restriction and base change.
Quasi-separatedness of the algebraic space also survives base change.

`exists_open_geometricComponentsEquiv_of_split_generic` then supplies an open
neighbourhood of the upstairs generic point on which the upstairs geometric
component sets are equivalent. The composite of the finite etale cover with
the open immersion is open. Its image of this neighbourhood is therefore a
nonempty open downstairs. For two points in that image, choose preimages in
the upstairs neighbourhood. Compose the inverse of
`GeometricComponentTransport.baseChangeGeometricFibreEquiv` at the first
preimage, the two upstairs comparisons through the generic point, and the
forward transport at the second preimage. This gives the claimed equivalence
of the actual downstairs geometric-fibre components. No descent of an
unspecified component model is assumed.

`exists_open_geometricFibreComponentCount` specializes to an irreducible
Noetherian affine base and applies `ENat.card_congr`. The resulting function
is exactly `geometricFibreComponentCount` from the host statement, including
all its values. Empty fibres require no exception.

Noetherian induction on closed base subschemes and approximation over
arbitrary rings remain separate obligations for the unrestricted host target.
The host statement and its import closure are unchanged.
