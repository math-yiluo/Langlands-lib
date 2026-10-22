# Closed normal restriction zero detection: proof

The module `Langlands.Cohomology.Continuous.ClosedSubgroupDescentProof` proves
the published proposition
`Langlands.Continuous.ClosedNormalRestrictionZeroDetection.{u}` from
`Langlands.Cohomology.Continuous.ClosedSubgroupDescentStatement`. The final
theorem `Langlands.Continuous.closedNormalRestrictionZeroDetection` has exactly
that type. The module does not change the statement module or anything it
imports.

It imports three modules:

- `Langlands.Cohomology.Continuous.ClosedSubgroupTopologyProof`, for the
  published topology helpers `exists_closedSubgroup_tuple_extension` and
  `exists_openNormal_tuple_agreement`. Through that module it also reaches
  `Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof`, which
  supplies `exists_covariant_quotient_factor`, `continuous_nestedEval` and the
  `moduleCycleClass` lemmas;
- `Langlands.Cohomology.Continuous.RestrictionMaps`, for
  `continuousRestrictionCochains`;
- the statement module.

## Setting and conventions

Everything is in the namespace `Langlands.Continuous` and uses one universe `u`.
The section variables are `k G : Type u`. Here `k` is a commutative ring with a
topology, and `G` is a topological group. Each lemma adds `[CompactSpace G]` and
`[TotallyDisconnectedSpace G]` only where noted. No declaration in the module
assumes `[T2Space G]`. The final theorem receives that instance from the target
proposition and does not use it.

Subgroups carry the subspace topology. Tuple spaces `Fin n → G` carry the
product topology. For `A : DiscreteModule k G` and `K : Subgroup G`, the
restricted module is the published `A.restrict K`, whose representation is
`TopRep.res K.subtype A.toTopRep`.

The cochain complex used throughout is
`underlyingContinuousCochains A.toTopRep`. This is the image of Mathlib's
`TopRep.homogeneousCochains A.toTopRep` under the forgetful functor
`forget₂ (TopModuleCat k) (ModuleCat k)`. A degree-`q` cochain is an invariant
element of `TopRep.resolutionX A.toTopRep (q + 1)`. `nestedEval` evaluates such
an element on `(q + 1)`-tuples, and it is injective (`nestedEval_injective`).
Restriction cochains are the published `continuousRestrictionCochains A K`. This
is the forgetful image of
`ContinuousCohomology.cochainsMap (subgroupInclusion K) (𝟙 _)`.

The file sets `backward.isDefEq.respectTransparency false`. Several `change`
steps unfold the published definitions to the Mathlib maps they abbreviate.

## Cochains, tuple functions and restriction

`exists_cochain_of_covariant` assumes `[CompactSpace G]`. Let `f` be a covariant
function on `(q + 1)`-tuples, that is, an element of
`covariantFunctions A.toTopRep (q + 1)`, and suppose `f` is continuous. Then
some degree-`q` cochain `v` satisfies
`nestedEval A.toTopRep (q + 1) v.1 = f.1`. Proof:

1. The Library theorem `exists_covariant_quotient_factor` gives an open normal
   subgroup `N`. It also gives a covariant function `F` on quotient tuples, with
   values in the fixed coefficients `finiteQuotientTopRep A N`, that agrees with
   `f` after coordinatewise projection.
2. The quotient `G ⧸ N` is discrete (`QuotientGroup.discreteTopology_iff`).
   Hence `nestedLift` turns `F` into a nested element, and `nestedLift_covariant`
   shows that this element is invariant. This gives a quotient cochain `w`.
3. Take `v` to be the image of `w` under the actual inflation cochain map
   `ContinuousCohomology.cochainsMap (quotientProjection N)
   (fixedCoefficientInclusion A N)` in degree `q`.
4. Its evaluation is computed with `nestedEval_resolutionMap`,
   `nestedEval_lift` and the agreement from step 1.

`nestedEval_restriction` holds for every subgroup `H`, with no compactness. It
states that evaluating the actual restriction
`(continuousRestrictionCochains A H).f q v` at a tuple `x : Fin (q + 1) → H`
gives `nestedEval A.toTopRep (q + 1) v.1 (fun i => (x i : G))`. The proof
unfolds the restriction to `ContinuousCohomology.resolutionMap` and applies
`nestedEval_resolutionMap`. The coefficient map is the identity.

`exists_openNormal_covariant_extension` assumes compactness and total
disconnectedness. Let `H` be a closed normal subgroup and let `f` be a
continuous covariant function for `A.restrict H.toSubgroup` on `n`-tuples. Then
there are an open normal subgroup `U` containing `H` and a continuous
`F : C((Fin n → G), A.toTopRep)` such that:

- `F` extends `f` on tuples from `H`;
- `F (fun i => g * x i) = A.toTopRep.ρ g (F x)` whenever `g ∈ U` and every
  `x i ∈ U`.

Proof:

1. `exists_closedSubgroup_tuple_extension` extends `f` to a continuous `F`. The
   discrete target is the coefficient space of `A`.
2. Define two continuous functions `L` and `R` on `(n + 1)`-tuples:
   `L x = F (fun i => x 0 * x i.succ)` and `R x = ρ (x 0) (F (Fin.tail x))`.
   Continuity of `R` uses the joint continuity `A.continuous_action`.
3. `L` and `R` agree on tuples from `H`, by the extension property and the
   covariance of `f`.
4. `exists_openNormal_tuple_agreement` gives `U`. Applying its agreement to
   `Fin.cons g x` yields the covariance identity.

## Boundaries and degree zero

`nestedEval_cochain_d` holds without compactness. It evaluates the differential
`(underlyingContinuousCochains A.toTopRep).d q (q + 1)` on a
`(q + 2)`-tuple `x`. The result is the alternating sum over `i` of
`(-1) ^ i • nestedEval … b.1 (x ∘ i.succAbove)`. The proof rewrites with
Mathlib's `TopRep.homogeneousCochains.d_apply` and the Library's `nestedEval_d`.

`exists_openNormal_restriction_cochain_zero` assumes only `[CompactSpace G]`;
total disconnectedness is omitted. Suppose a degree-`q` cochain `c` has zero
restriction to a closed normal subgroup `H`. Then it has zero restriction to
some open normal subgroup `U` containing `H`. Proof:

1. The evaluation of `c` is a continuous function on tuples, by
   `continuous_nestedEval`. By `nestedEval_restriction` it vanishes on tuples
   from `H`.
2. `exists_openNormal_tuple_agreement`, comparing it with the zero function,
   gives `U`.
3. `Subtype.ext` and `nestedEval_injective` for `A.restrict U.toSubgroup`
   reduce the claim to tuple evaluation. That case is step 2, via
   `nestedEval_restriction` again.

`exists_openNormal_restriction_boundary` treats positive degrees. Let `c` be a
cochain of degree `q + 1`, and let `b` be a degree-`q` cochain of
`A.restrict H.toSubgroup` with `d b` equal to the restriction of `c`. Then for
some open normal `U ⊇ H` there is a degree-`q` cochain `w` of
`A.restrict U.toSubgroup` with `d w` equal to the restriction of `c` to `U`.
Proof:

1. The evaluation of `b` is covariant (`nestedEval_invariant`) and continuous.
   Here `H` is given its topological-group and compact-space instances.
   `exists_openNormal_covariant_extension` gives `U` and an extension `F` that
   is covariant on tuples from `U`.
2. Let `D` be the alternating deletion sum of `F` on `(q + 2)`-tuples, and let
   `C` be the evaluation of `c`. Both are continuous.
3. Evaluating `hb` with `nestedEval_cochain_d` and `nestedEval_restriction`,
   and using that `F` extends `b`, shows that `D` and `C` agree on tuples from
   `H`.
4. `exists_openNormal_tuple_agreement` gives `V` on which `D` and `C` agree.
5. Let `W = U ⊓ V`. It is compact, because an open subgroup is closed. The
   restriction of `F` to tuples from `W` is continuous and covariant, using the
   `U`-component of membership. `exists_cochain_of_covariant` for
   `A.restrict W.toSubgroup` turns it into a genuine cochain `w`.
6. By `nestedEval_injective`, the identity `d w = (restriction of c to W)` is
   checked on tuples. There the left side is `D` (by `nestedEval_cochain_d`),
   `D` equals `C` (by the `V`-component of membership), and `C` is the right
   side (by `nestedEval_restriction`).

`exists_openNormal_restriction_boundary_sc` restates the boundary descent for
the degree-`q` short complexes `(underlyingContinuousCochains _).sc q`, where
`X₁ = X (prev q)` and `f = d (prev q) q`. It covers every `q`, by `cases q`:

- **Degree zero.** In `ComplexShape.up ℕ` there is no relation from `prev 0` to
  `0`, so the incoming map `dTo 0` is zero (`HomologicalComplex.dTo_eq_zero`,
  with `CochainComplex.prev_nat_zero`). The hypothesis then says that the
  restriction of `c` to `H` is zero.
  `exists_openNormal_restriction_cochain_zero` gives `U` on which the
  restriction of `c` is zero. The required primitive is `w = 0`.
- **Successor degree `q + 1`.** Rewrite `prev (q + 1)` to `q` with
  `CochainComplex.prev_nat_succ` in both the hypothesis and the goal, then
  apply `exists_openNormal_restriction_boundary`.

## Module homology and homology naturality

`exists_openNormal_restriction_homology_zero` works in the actual module
homology `(underlyingContinuousCochains A.toTopRep).homology q`. Suppose a class
`x` has `HomologicalComplex.homologyMap (continuousRestrictionCochains A H) q x
= 0`. Then for some open normal `U ⊇ H` the same holds for
`continuousRestrictionCochains A U.toSubgroup`. Proof:

1. For a subgroup `K`, let `φ K` be the map of degree-`q` short complexes
   induced by `continuousRestrictionCochains A K`, through
   `HomologicalComplex.shortComplexFunctor`.
2. `moduleCycleClass_surjective` writes `x` as the class of a cycle `c`. The
   commutativity `(φ K).comm₂₃` shows that `(φ K).τ₂ c` is a cycle.
3. `moduleCycleClass_naturality` identifies the restricted class with the class
   of `(φ K).τ₂ c`, for `K = H` and later for `K = U`. Here the complex-level
   `homologyMap` in degree `q` is the `ShortComplex.homologyMap` of `φ K`.
4. `moduleCycleClass_eq_zero_iff` turns the hypothesis into a primitive over
   `H`. `exists_openNormal_restriction_boundary_sc` moves it to a primitive
   over `U`, and the same criterion shows that the class over `U` is zero.

`continuousRestriction_homology_comparison` holds for every subgroup `H`,
without compactness or total disconnectedness. It compares actual continuous
cohomology with module homology. Write `e` for the canonical isomorphism
`ShortComplex.mapHomologyIso` of the degree-`q` short complex of
`TopRep.homogeneousCochains` along `forget₂ (TopModuleCat k) (ModuleCat k)`.
Its inverse sends the forgetful image of continuous cohomology to module
homology. The theorem states that the inverse isomorphism for `A.restrict H`,
applied to `continuousRestriction A H q x`, equals
`HomologicalComplex.homologyMap (continuousRestrictionCochains A H) q` applied
to `e.inv x`. It is Mathlib's `ShortComplex.mapHomologyIso_inv_naturality` for
the short-complex map induced by
`ContinuousCohomology.cochainsMap (subgroupInclusion H) (𝟙 _)`, evaluated at `x`
with `ConcreteCategory.congr_hom`. The published `continuousRestriction` is
`ContinuousCohomology.map` along that same cochain map.

`exists_openNormal_continuousRestriction_zero` assumes compactness and total
disconnectedness. Suppose `continuousRestriction A H.toSubgroup q x = 0`. The
comparison theorem and `map_zero` show that the restricted module class of
`e.inv x` is zero. The previous theorem gives `U` on which the restricted module
class of `e.inv x` is also zero. By the comparison theorem for `U`, the inverse
isomorphism for `A.restrict U.toSubgroup` sends
`continuousRestriction A U.toSubgroup q x` to zero. This inverse is injective,
since it is a monomorphism in `ModuleCat` (`ModuleCat.mono_iff_injective`), so
`continuousRestriction A U.toSubgroup q x = 0`. The conclusion uses the
published `continuousRestriction`, not a replacement map.

`closedNormalRestrictionZeroDetection` introduces the quantified ring, group,
eight instances (including the unused `T2Space G`), module, subgroup, normality
instance, degree, class and hypothesis. It then applies
`exists_openNormal_continuousRestriction_zero`. All degrees, including
`q = 0`, are covered.

Development inspection of the final theorem reports universe parameter `u` and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and scope

This proof is an internal derivation. The statement module's Markdown gives the
mathematical provenance: Serre, *Local Fields*, X §3 and XII §1, Theorem 1. It
also records the expected locally-constant cochain route, which this module
implements in the form described above. The proof itself cites no literature.
It uses only:

- the published Library cochain-evaluation, finite-quotient and cycle-class
  lemmas named above;
- the published topology helpers;
- Mathlib's homological algebra.

It proves or assumes no arithmetic vanishing theorem, Brauer-group
identification, inflation–restriction exactness or field lifting. Those are
separate inputs to the intended local unramified H² application.

Worker 102 wrote the Lean proof in a shared draft for task `3263cf33`. The draft
file is byte-identical across revisions 4–6, and it is submitted unchanged.
Worker 284 rewrote this Markdown for submission, replacing the draft's
development-status wording with a description of the submitted proof.
