# The glued topological space of gluing data along open subspaces

For gluing data `R : LocalizedOpenRelation K` (module `LocalizedOpenRelation`),
this module constructs the underlying topological space of the glued analytic
space. Namespace: `Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation`.

## Construction

- `Space R` is the quotient of the disjoint union `Σ m, |Z m|` of the points of the
  pieces by `pointSetoid` (two points are identified when a point of `S m n`
  projects to both), with the quotient topology.
- `ι m : |Z m| → Space R` is the quotient map on the piece `m`.

## Results

- `continuous_ι`; `ι_eq_ι_iff`: `ι m z = ι n z'` exactly when some point of `S m n`
  projects to `z` and `z'`; `ι_a_eq_ι_b`.
- `injective_ι`: on one piece the relation is equality, because `a m m = b m m`.
- `preimage_ι_image_ι`: the trace on `Z n` of the image of `U ⊆ Z m` is
  `b m n (a m n⁻¹(U))`. It is open when `U` is open, since `b m n` is an open
  embedding, so `ι m` is an open map (`isOpenMap_ι`) and an open embedding
  (`isOpenEmbedding_ι`).
- `preimage_range_ι`: the trace on `Z m` of the image of `Z n` is `domainSet m n`.
- `exists_ι_eq`: every point of `Space R` comes from some piece.
- `Rel.ι_apply`: related morphisms have the same points in `Space R`.

## Provenance

Derived from the proof of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Proposition 1.3.3, printed p.24 / PDF p.21
(`berkovich-1993-etale-cohomology`): the glued space is the quotient of the disjoint
union by the equivalence relation of the gluing data, and in case a) the relation is
open, so that the pieces map onto open subsets.
