# The slice of a small étale site

This module constructs the equivalence between the slice of a scheme's small
étale site over an étale object and the small étale site of that object's
underlying scheme. It proves the covering comparisons and transports
sheafification and the category of module sheaves. This supplies a reusable
prerequisite for derived coefficients localized to a source torsor.

## Inputs and conventions

Let `X : Scheme.{u}` and `V : X.Etale`. The structural map `V.hom` is étale;
it need not be finite or surjective. `Over V` is the ordinary categorical slice
inside `X.Etale`, with topology `X.smallEtaleTopology.over V`. The other site is
`V.left.Etale` with `V.left.smallEtaleTopology`. Both are actual Mathlib
categories of schemes and commutative triangles.

For the module constructions, `R : Type u` is a ring, and the coefficient
category is `ModuleCat.{u} R`. Commutativity, finite generation and inversion of
a group order are not required. The scheme, ring carrier and module carriers
use the same universe `u`; the construction does not enlarge module carriers to
the object universe of the slice site.

## The categorical equivalence

`toSmallEtale V` sends an object `U` of `Over V` to the scheme `U.left.left`
with structural map `U.hom.left` to `V.left`. A morphism between étale
`X`-schemes is étale by Mathlib's small-étale-category instances. The map on
arrows retains the underlying scheme morphism; its triangle identity follows
from `Over.w`.

`fromSmallEtale V` sends an étale `V.left`-scheme with structural map `a` to
the étale `X`-scheme with structural map `a ≫ V.hom`, together with its map to
`V`. On morphisms it retains the underlying scheme morphism and proves the
two triangle identities.

`siteEquivalence V : Over V ≌ V.left.Etale` uses these functors. Its unit and
counit have identity underlying scheme maps. The unit's structural-map equality
uses `MorphismProperty.Over.w U.hom`, since the reconstructed structural map to
`X` is a composite rather than definitionally the original map. Naturality and
the equivalence coherence are the identities of these underlying maps.

## Covering sieves

`mem_sliceTopology_iff` characterizes a covering sieve `S` on `U : Over V` by
the following condition: every point `x` of `U.left.left` is the image of a
point `w` along an arrow `f : W ⟶ U` belonging to `S`. These are points of
the underlying scheme topological spaces.

The proof rewrites Mathlib's slice-topology membership criterion and the
published `EtaleAutomorphism.mem_smallEtaleTopology_iff`. An arrow over the
underlying object lifts to the slice by composition with `U.hom`; in the other
direction its image belongs to the pushed-forward sieve using the identity
factorization.

`toSmallEtale_isCocontinuous` and `fromSmallEtale_isCocontinuous` prove
cocontinuity in both directions for the stated topologies. Given a point and
an arrow of a covering sieve, each proof constructs a domain object and a map
in the source site with the same underlying scheme map. The image arrow
factors through the given sieve arrow via a map with identity underlying
scheme map. Downward closure of the sieve supplies membership, and the
original point equality supplies the covering condition.

`siteEquivalence_inverse_isDenseSubsite` applies Mathlib's theorem that the
inverse of a categorical equivalence, cocontinuous in both directions, is a
dense subsite. This is proved from the two covering constructions, with no
assumed comparison of topologies.

## Module sheaves and sheafification

`moduleHasSheafify V R` transports `HasSheafify` from the small étale site of
`V.left` to `X.smallEtaleTopology.over V` using
`CategoryTheory.Equivalence.hasSheafify`. The source instance is Mathlib's
actual small-étale sheafification, obtained through its essentially small
affine étale site in `AlgebraicGeometry/Sites/AffineEtale.lean`.
The transported construction is a left adjoint to the inclusion of sheaves
into presheaves and preserves finite limits, as required by `HasSheafify`.
Together with the imported sheaf-category results, it makes the existing
abelian-category instance available for these slice module sheaves.

`moduleSheafEquivalence V R` is the resulting actual equivalence

```text
Sheaf (X.smallEtaleTopology.over V) (ModuleCat R)
  ≌ Sheaf V.left.smallEtaleTopology (ModuleCat R).
```

It specializes Mathlib's `Equivalence.sheafCongr`. Its forward functor
precomposes a slice sheaf with `(fromSmallEtale V).op`; its inverse precomposes
with `(toSmallEtale V).op`. Its unit and counit come from the categorical
equivalence above.

## Provenance and scope

This is an internal construction from the published
`Langlands.Geometry.EtaleAutomorphism` pointwise covering criterion and the
pinned Mathlib implementations in `CategoryTheory/Sites/Over.lean`,
`CategoryTheory/Sites/Equivalence.lean`,
`CategoryTheory/MorphismProperty/Comma.lean` and
`AlgebraicGeometry/Sites/AffineEtale.lean`. The explicit functors and pointwise
covering proofs justify their specialization here; no new assertion is
attributed to an external mathematical source.

The module constructs the site and sheaf-category equivalences on supplied
schemes. It does not construct Harris's schemes or torsors, derived sections,
compact support, or a geometric uniformization comparison. Those remain
separate parts of the Harris framework.
