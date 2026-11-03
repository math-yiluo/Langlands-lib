# Actions and dimensions on specified smooth fppf quotients

This is an internal derived construction connecting the existing all-test
`IsFppfQuotient` interface to the action and dimension data used in relative-root
induction. It constructs an action on a supplied quotient. Quotient existence,
affineness of the quotient, and the smooth relative dimension of its projection
remain explicit inputs.

## Actual objects and hypotheses

The general-base results use an arbitrary scheme `B : Scheme.{u}`, actual group
schemes `H`, `G`, `Q` over `B`, an actual homomorphism `q : G ⟶ Q`, a subgroup
functor `N`, and `hq : IsFppfQuotient N q`. The latter is the existing definition
in `Rational.RootSubgroupStructureStatement`: the underlying scheme morphism of
`q` is flat, surjective, and locally of finite presentation, and the range of its
actual scheme-theoretic kernel inclusion equals `N` on every scheme test. It
does not assert surjectivity on each original test's point group.

The action construction additionally assumes that the underlying scheme map of
`q` is quasi-compact and that `N` is stable under a given
`a : AutomorphicAction H G`. No centrality, field, smoothness, connectedness or
affineness assumption is needed for this construction.

The field results allow every field `k : Type u`. Unipotence means exactly the
existing `IsUnipotent` representation predicate. It is not replaced by a claim
about geometric points or by an unproved geometric characterization.

## Provenance

The module derives its results from existing Lean definitions and proofs:

- `AutomorphicAction.IsEquivariant` and `SubgroupFunctor.range` give stability
  of the range of an equivariant homomorphism.
- `AutomorphicAction.onQuotient`, its all-test equivariance and its bundled
  uniqueness theorem supply the descended action from flatness, surjectivity,
  quasi-compactness and stability of the actual kernel.
- `IsUnipotent.of_flat_surjective` descends the existing representation
  predicate along the supplied quotient.
- `Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp`
  descends smoothness through the smooth surjective quotient projection.
- `Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension` supplies a
  constant smooth relative dimension on a connected smooth quotient.
- `Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension` identifies
  the Krull dimension of a closed-point stalk with each given smooth relative
  dimension, allowing their comparison.
- Mathlib supplies connectedness of a continuous surjective image, existence
  of a closed point in a nonempty Jacobson scheme, composition of smooth
  relative dimensions, and quasi-compactness of a map between the affine
  schemes in the concluding theorem.

No additional external structural assertion is used. These are supporting
adapters for the unchanged ordered-product problem.

## Stability, action and connectedness

`AutomorphicAction.IsEquivariant.isStable_range` takes an equivariant map
`z : Z ⟶ G`. An element of its range on a test is represented by a point `v` of
`Z`; acting on `v` supplies a representative for the acted-on image, by
equivariance. This proves stability on every scheme test.

`IsFppfQuotient.connectedSpace` sends connectedness of `G` to `Q` using the
surjectivity component of `hq` and continuity of the underlying scheme map.
It does not require quasi-compactness or an action.

The entry definition `IsFppfQuotient.action hq a hN` applies
`AutomorphicAction.onQuotient` after rewriting stability of `N` by the exact
kernel-range equality in `hq`. The accompanying theorems establish:

- `action_isEquivariant`: `q` intertwines the original and descended actions
  on every test;
- `action_act`: for every `T : Over B`, `h : T ⟶ H.X` and `g : T ⟶ G.X`,
  `(hq.action a hN).act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom`;
- `action_unique`: any bundled automorphic action on `Q` making `q`
  equivariant equals this action.

The formula specifies behavior on lifted points; the imported construction
proves the action laws on all points by fpqc descent. No global point-lifting
assumption is introduced.

## Unipotence and dimension data over fields

`IsFppfQuotient.isUnipotent` applies `IsUnipotent.of_flat_surjective` to the
flat and surjective components of `hq`. It needs neither quasi-compactness nor
smoothness.

The private lemma `relativeDimension_eq` compares two prescribed smooth
relative dimensions of the same nonempty scheme over a field. Smoothness makes
the scheme locally of finite type over a field, hence Jacobson. A closed point
exists. Applying `fieldSmoothClosedPointStalkDimension` twice at that point
gives equality of the dimensions as natural numbers. No affine or connected
hypothesis is needed for this private comparison.

`IsFppfQuotient.exists_action_relativeDimension` assumes that `G` and `Q` are
affine over `k`, that `G` is connected and unipotent, and that the supplied
projection `q` is an fppf quotient by the `a`-stable subgroup `N`. It also takes
`SmoothOfRelativeDimension d G.X.hom`,
`SmoothOfRelativeDimension n q.hom.hom.left`, and `0 < n`.
It produces an actual action `b : AutomorphicAction H Q` and `m : ℕ` with
smoothness, connectedness and unipotence of `Q`,
`SmoothOfRelativeDimension m Q.X.hom`, `d = n + m`, `m < d`, and the displayed
all-test action formula for `b`.

The proof first descends smoothness through `q`, transfers connectedness by
surjectivity, and obtains `m` from the smooth connected relative-dimension
result. Composition gives relative dimension `n + m` for `G`; the private
closed-point comparison identifies this with `d`. Positivity of `n` gives the
strict inequality. Affineness of `G` and `Q` supplies quasi-compactness of `q`,
so the entry construction supplies `b`. Unipotence descends as above.

This theorem supplies the consequences of specified quotient geometry. It does
not construct the quotient, prove its affineness, or derive the projection's
relative dimension from a central vector subgroup. It therefore does not prove
`CentralSmoothQuotientStatement` or `SemigroupOrderedProductStatement`.
