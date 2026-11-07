# Existence of root maps normalized by a supplied split pinning

Authors: Worker 1354 (proof implementation and documentation) and Worker 1375
(source and constraint audit).

`Langlands.GroupScheme.normalizedRootExistence.{u}` proves exactly the published
`Langlands.GroupScheme.NormalizedRootExistenceStatement.{u}`. For every field
`k : Type u`, actual affine group scheme `G` over `Spec k`, and supplied
`p : SplitPinning G`, its conclusion is

```lean
Nonempty p.NormalizedSimpleRootParametrizations ∧
  Nonempty p.SimpleReflectionRepresentatives
```

No additional hypothesis is retained. The proof preserves arbitrary
characteristic, finite and imperfect fields, arbitrary universe `u`, and empty
simple-root support. It changes neither the statement pair and its imports nor
the parent `QuasiSplitSteinbergQuotientStatement` pair and its imports.

The proof is an internal deduction from existing Library results about the
intrinsic root functor, natural vector coordinates, actual dual-number Lie
kernels, and root-scaling automorphisms. Its source-motivated assertion is the
derived scheme-theoretic and Lie-normalized translation described in
[NormalizedRootExistenceStatement.md](NormalizedRootExistenceStatement.md).
Borel–Springer, *Rationality properties of linear algebraic groups II* (1968),
§§8.1–8.2, printed pp.481–482 / PDF pp.39–40, registered as
`borel-springer-1968-rationality-properties-ii`, gives additive root
parametrizations, their torus equivariance, and rationality for a split torus.
The implementation uses the already published intrinsic-functor and Lie
comparisons rather than repeating that geometric argument. It normalizes by
postcomposing an automorphism of `G`, as detailed below.

For a simple index `a`, `p.root_mem_relativeRoots a` gives a nonzero actual
root, and reducedness in the supplied root datum gives
`p.hasNoHigherRoots a`. Connected reductivity supplies smoothness of `G`.
`RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero` supplies an actual
representative `j : U ⟶ G` of the entire intrinsic root subgroup functor and
its closed immersion. Closedness makes `U` affine.

`RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots` supplies a
finite dimension `n` and natural group isomorphisms

```lean
e T : (T ⟶ U.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))
```

whose torus action is multiplication by the actual root character, on every
scheme `T` over `Spec k`. Compose the inverse linear coordinates on the actual
Lie kernel with `RelativeRoot.representedRootLieEquiv` and the inverse supplied
pinning trivialization. This gives a linear equivalence
`(Fin n → k) ≃ₗ[k] k`; equality of finite ranks forces `n = 1`.
The natural-coordinate isomorphism
`E := RelativeRoot.vectorGroupIso e he.1` therefore identifies `U` with the
standard additive group. Put `f₀ := E.inv ≫ j`.

Precomposition by an isomorphism preserves the whole range subgroup functor
and a closed immersion, so `f₀` represents the intrinsic root subgroup and
is closed. The inverse-coordinate identity for `E` identifies a standard
scalar point with the corresponding `e` coordinates. The weight formula
for `e`, together with `RelativeRoot.subgroupAction_act_comp`, then proves
the required conjugation formula for `f₀`. These equalities quantify over
all schemes over `Spec k` and their global functions, including nonreduced
and nonaffine tests.

`VectorGroup.standardEpsilon_ne_zero` observes that the actual epsilon vector
has Lie coordinates constantly equal to `1`, so it cannot be zero. Compose
`RelativeRoot.representedRootLieEquiv` for `f₀` with the inverse pinning
trivialization to obtain a linear equivalence `L` with `k`. Set
`c := L (VectorGroup.standardEpsilon k)`. Injectivity gives `c ≠ 0`.
The underlying-map formula for the root Lie equivalence and
`RootPinning.trivialization_apply_val` show that the actual derivative of `f₀`
sends standard epsilon to `c • p.pinning.rootVector a`.

Let `s` be the constant tuple of units with value `c⁻¹`, and set
`σ := p.rootScalingIso s`. This is an actual group-scheme automorphism fixing
the supplied torus inclusion. Its actual differential multiplies the pinned
vector at `a` by `c⁻¹`. Define the normalized map to be `f₀ ≫ σ.hom`.
The restriction `τ := RelativeRoot.rootIsoOfFixesTorus ... σ ...` is an
automorphism of the represented root subgroup satisfying
`τ.hom ≫ f₀ = f₀ ≫ σ.hom`. This identity preserves the full range subgroup
functor; composition with `σ` also preserves closedness. Postcompose the
conjugation formula for `f₀` by `σ` and use torus fixation to get the formula
for the normalized map. Finally, postcomposition of actual dual-number
points proves the differential composition formula, and linearity reduces
the derivative to

```lean
c • (c⁻¹ • p.pinning.rootVector a) = p.pinning.rootVector a.
```

This proves `SplitPinning.nonempty_normalizedRootParametrization` for every
simple index. The selected automorphism is used separately for each index;
the target imposes no compatibility between these choices.

`SplitPinning.simpleReflectionRepresentative` chooses the witnesses already
contained in `p.isRootDatum.2.2 a`: a rational normalizing point, an actual
torus automorphism, its normalization equality, and its character action
equal to the simple reflection. The character action retains the Library's
inverse-automorphism convention. Choice of the root parametrizations and
these reflection witnesses gives the two families in the closing theorem.

No braid relations, Galois compatibility, pinning existence, cross-section
geometry, invariant-quotient comparison, or global rational section for
arbitrary quasi-split groups is asserted.
