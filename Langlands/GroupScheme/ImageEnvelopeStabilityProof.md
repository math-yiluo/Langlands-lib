# Stability of closed image envelopes

Author: Worker 1372.

`Langlands.GroupScheme.pointedImageEnvelopeStability` proves the exact published
proposition `Langlands.GroupScheme.PointedImageEnvelopeStabilityStatement.{u}`
from `ImageGenerationStatement`, for arbitrary universe `u`. Its conclusion is
stability of the existing `closedImageEnvelope f` on every test scheme,
including nonreduced schemes, under the given actual split-torus action.

This is an internal derived proof. The source motivation and the derived
pointed-morphism formulation are recorded in `ImageGenerationStatement.md`.
The implemented argument uses the published universal closed-factorization
locus from `Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof` and
Yoneda transport from `RepresentabilityTransfer`. It proves stability directly
from the defining intersection and does not depend on pointed-image generation
or on existence of a representative of that intersection.

For an automorphic action `b` of a group scheme `H` on `G` and a subgroup
functor `F`, `AutomorphicAction.orbitCore b F` consists of the points
`g : T ⟶ G.X` such that

```lean
∀ (T' : Over B) (c : T' ⟶ T) (h : T' ⟶ H.X),
  b.act h (c ≫ g) ∈ F.carrier T'
```

The action preserves identity, products and inverses, so this condition defines
a subgroup on each test scheme. Its quantification over refinements gives
functoriality. The elementary lemmas establish that:

- `orbitCore_le` puts the core inside `F` by taking the identity refinement
  and the identity element of the acting group.
- `mem_orbitCore_iff_universal` detects the condition at the universal point of
  `H.X ⊗ T`. One direction specializes the refinements; the other pulls back
  along `lift h c` and uses naturality of the action.
- `orbitCore_isStable` combines two acting points using the action's
  multiplication law.
- `orbitCore_containsImage` puts an equivariant source image in the core
  whenever it lies in `F`: every translate of an image point is again the
  image of a translated source point.

`orbitCore_range_isClosedRepresentable` proves the geometric step over an
arbitrary field `k`, assuming only that `H.X.hom` is affine. Given an actual
closed subgroup `i : K ⟶ G`, form the pullback

```lean
D := pullback b.hom i.hom.hom
d := pullback.fst b.hom i.hom.hom
```

Thus `d : D ⟶ H.X ⊗ G.X` is a closed immersion: it is the inverse image of the
closed subgroup under the actual action morphism. Over a field the coordinate
module of `H.X` is projective, with the identity faithfully flat algebra
extension as witness; structural flatness is automatic. The published
`ClosedFactorizationLocusProof.closedFactorizationLocus` therefore supplies a
closed immersion `j : Z ⟶ G.X` whose points are exactly the maps `g` such that
the entire product `H.X ◁ g` factors through `d`.

The pullback universal property identifies this product-factorization condition
with the universal acting point lying in the range of `i`. Combined with
`mem_orbitCore_iff_universal`, it yields, for every test scheme,

```lean
g ∈ (b.orbitCore (SubgroupFunctor.range i)).carrier T ↔
  ∃ z : T ⟶ Z, z ≫ j = g
```

`SubgroupFunctor.isClosedRepresentable_of_scheme` then transports the subgroup
structure to `Z` and produces an actual closed group-scheme inclusion
representing this core. The all-test universal property of the
closed-factorization locus is essential here: the argument retains the scheme
structure of the full product and uses no restriction to rational or reduced
points.

`AutomorphicAction.closedImageEnvelope_isStable` proves the stronger result for
any affine acting group over a field, any ambient group scheme and any
equivariant source morphism. Fix a test point `g` in the envelope and an
arbitrary closed subgroup `i` through which `f` factors. Equivariance puts the
image of `f` in the orbit core of the range of `i`. That core is represented by
an actual closed subgroup, so
`closedImageEnvelope_le_of_containsImage` puts the entire envelope inside it.
Evaluating the defining core condition at the identity refinement shows that
every translate of `g` lies in the range of `i`. Since `i` was an arbitrary
competitor in the defining intersection, every translate of `g` lies in the
same envelope.

Finally, `pointedImageEnvelopeStability` introduces all hypotheses of the
published target and applies this stronger lemma. The affine hypothesis on the
acting group is discharged by `IsSplitTorus.isAffineHom` from
`Torus.SplitReductiveProof`. The target's smoothness, source regularity,
finite-type and pointing hypotheses are retained in its exact type but are
unneeded by this argument. The proof imposes no characteristic, perfectness or
separability condition and does not assert the separate geometric generation
conclusions.
