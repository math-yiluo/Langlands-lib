# Direct image on small etale sites for arbitrary scheme morphisms

This module constructs direct image of sheaves along an arbitrary scheme morphism
`f : Z ⟶ X`. It uses the actual scheme fiber-product functor on small etale objects
from `Langlands.Shimura.Coefficients.EtaleTorsorPullback`; it proves that functor
continuous and then precomposes sheaves. This is internal categorical
infrastructure derived from the existing geometric pullback and Mathlib's
restricted-site constructions. It makes no new external-literature claim.

Both schemes have universe `u`. The coefficient category `A : Type uA` has
morphisms in the independently chosen universe `vA`. The general direct-image
construction requires only `[Category A]`; it imposes no completeness,
smallness, abelianity or sheafification hypothesis on `A`. The linear
specialization takes `R : Type u` with `[CommRing R]` and modules with carriers
in universe `u`. No etaleness assumption is imposed on `f`.

## Geometric base change and continuity

Write `P_f : X.Etale ⥤ Z.Etale` for `etaleObjectPullback f`. It sends
`(U ⟶ X)` to `(U ×_X Z ⟶ Z)` and sends morphisms to their actual scheme
base changes. Its source and target consist of etale structure morphisms.

`objectPullback_preservesFiniteLimits` specializes Mathlib's finite-limit
preservation instance for `MorphismProperty.Over.pullback` to the etale
morphism property. Thus it also establishes representable flatness.

`objectPullback_coverPreserving` proves preservation of covering sieves.
The small etale topology is the restricted topology from the etale topology
on the ordinary over-category. Forgetting a small etale object to that
over-category preserves covering sieves. The square formed by forgetting and
pulling back commutes definitionally: both composites are ordinary
over-category base change. Ordinary over-category base change preserves
covering sieves by
`GrothendieckTopology.coverPreserving_overPullback`. The proof rewrites
pushforward of a sieve along that composite and applies these two
cover-preservation results successively.

`objectPullback_isContinuous` combines cover preservation and representable
flatness using `Functor.isContinuous_iff_coverPreserving`. Consequently
precomposition by `P_f.op` carries sheaves on `Z` to sheaves on `X`.

## The direct-image functor

`directImage f A` is the resulting functor

```text
Sheaf Z.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A.
```

Its underlying presheaf is `P_f.op ⋙ F.obj`. In particular the lemma
`directImage_obj_obj` identifies its value on a small etale `X`-scheme `U`
with `F(U ×_X Z)`. The lemma `directImage_map_app` identifies its action
on a sheaf morphism with the original morphism evaluated on that same
base-changed test object. These are definitional equalities, including
the induced restriction maps.

For `A = ModuleCat R`, `directImage_additive` and `directImage_linear`
prove that this functor preserves addition and `R`-scalar multiplication
on sheaf morphisms. Both proofs use extensionality of sheaf morphisms
and the pointwise operations on module-valued natural transformations.

The construction supplies actual arbitrary-morphism direct image. An inverse
image with a constructed adjunction, its comparison with the existing
restriction along an etale map, composition and identity coherence,
algebraic-closure base change, derived images, support comparisons and
the Harris-specific coefficient systems remain separate constructions.
