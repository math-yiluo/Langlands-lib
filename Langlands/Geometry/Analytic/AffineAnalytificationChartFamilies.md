# Compatible algebra maps on source charts

This internal construction supports the affine analytification fibre-product
proof. For a complete ultrametric nontrivially normed field `K`, a commutative
`K`-algebra `A`, a finite polynomial presentation `P` of `A`, and a saturated
source `S : SaturatedAtlasPresentation.{u,u,u} K`, `toAlgebraFamily P` reads
from a complete strong morphism `S ⟶ saturated K P` an algebra map
`A →ₐ[K] S.presentation.atlas.algebra i` on every source chart. The algebra
`A` may lie in any universe. The structure `AlgebraFamily` requires these maps
to commute with every bounded source restriction. These are equalities of
algebra maps, retaining information in nonreduced algebras.

The construction uses the published polynomial-locus restrictions and their
values on the coordinate algebra. Original polynomial charts remain in the
saturation, with equal presented algebras; bounded identity casts express those
equalities. Every saturated target chart is contained in its original parent,
so a strong morphism admits original polynomial target charts. Directedness
compares any two such choices in a common upper chart, proving independence.
The source restriction equation then gives the compatible family. In Lean,
`coordinate_triangle` and `coordinate_square` prove the requisite elementary
composition identities for arbitrary presented algebras before specializing
them to these atlases. `chartAlgHom_independent` establishes independence of
the chosen original target; `chartAlgHom_naturality` establishes the source
restriction equation. No identification of algebra maps by their values on
spectrum points is used.

This is derived infrastructure for the Library model, rather than a separate
assertion in the literature. Its provenance is the published polynomial-locus
atlas construction, the full original-chart restriction identities in
`CompatibleStrongOriginalRestriction`, and the defining naturality of complete
strong maps. Its intended application is the chartwise proof of the affine
fibre-product compatibility recorded in `AffineAnalytificationFibreProductStatement`;
the present module establishes only extraction, without claiming reconstruction
or the fibre-product statement itself.
