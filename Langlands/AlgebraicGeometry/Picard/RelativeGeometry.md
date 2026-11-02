# The family of base changes of a scheme with a section

For `f : X → S`, `Langlands.AlgebraicGeometry.Picard.relativeSpace f` is the
functor on actual `S`-schemes that sends `T` to `T ×_S X`. It is the existing
Mathlib slice-category pullback functor `Over.pullback f` followed by forgetting
the map to `X`; its identity and composition laws are inherited from those
functors. The ordering of the factors is a convention.
`relativeSpaceSymmetry f T` is the canonical isomorphism with `X ×_S T`.

The natural transformation `relativeProjection f` sends each fibre product
to `T` by its first projection. Given an actual section `ε : S → X` and the
equation `ε ≫ f = 𝟙 S`, `relativeSection` constructs the natural transformation
from `T` to `T ×_S X` using the pullback universal property, with components
`(id_T, ε ∘ T.hom)`. The two projection identities are proved in
`relativeSection_projection` and `relativeSection_snd`. In particular, each
component is a section of the corresponding base-changed structure morphism.
Naturality is proved by equality of both projections into the fibre product;
its equation is exactly the square needed when pulling back rigidifications.

`relativeSpace_map_snd` states that the map induced by a morphism of
`S`-schemes preserves the projection to `X`, including its `@[reassoc]`
variant. It is the unchanged general projection identity moved from
`RigidifiedClassesNoetherianApproximationReductionProof` to this common
geometry module and renamed into the present namespace. The approximation
proof and `RelativePointLifts` both reuse it.

## Provenance and scope

This is derived categorical infrastructure for Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, preliminary draft, Chapter VI §1, paragraph (6.2),
printed p.88 (PDF p.92), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
That passage uses the induced section `ε_T : T → X ×_S T` and its naturality
under morphisms of `S`-schemes in order to pull back rigidified bundles. The
present definitions implement the scheme maps alone, using Mathlib's actual
scheme fibre products and their universal property. The canonical symmetry
accounts for our factor ordering. No line-bundle, Picard, or representability
assertion is made by this module.
