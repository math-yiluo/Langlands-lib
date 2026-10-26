# Absolute continuous corestriction

Authors: Worker 42, with Worker 134's adapted coefficient-transport construction.

`Langlands.ClassFieldTheory.Local.absoluteCorestriction K L q` constructs
corestriction from the underlying module of `absoluteCohomology L q` to that
of `absoluteCohomology K q`. These are the actual continuous cohomology groups
of the absolute Galois groups with discrete algebraic-closure unit
coefficients. The map is linear over `IntegerScalars` (the lifted integer
ring), hence additive. It is a `ModuleCat` morphism; continuity between the
topological cohomology objects is not asserted.

Here `K L : Type u` are fields in an arbitrary common universe, with
`CharZero K`, `Algebra K L`, and `FiniteDimensional K L`. The supplied
`Algebra (AlgebraicClosure K) (AlgebraicClosure L)` and
`IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)` specify the
closure embedding used by every map. There is no normality hypothesis on
`L/K`, additional closure tower over `L`, or assumed invertibility or
transfer law. The degree `q : ℕ` includes zero. In particular the signature
applies to every finite extension between p-adic fields represented in a
common universe, for every prime. It is not restricted to carriers in
`Type 0`; independent lower and upper universes are not supported here.

## Coefficient and cohomology transport

Write `G_K = Field.absoluteGaloisGroup K`,
`H = AbsoluteRestriction.openSubgroup K L`, and
`A = absoluteUnitDiscreteModule K`. The imported `AbsoluteRestrictionImage`
module proves that `H` is the actual image of the specified absolute Galois
restriction, and supplies
`AbsoluteRestriction.groupEquiv K L : G_L ≃ₜ* H`.
The bundle `A`, imported from `FixedFieldStages`, has underlying
representation `absoluteUnits K`.

The following names lie in the namespace
`Langlands.ClassFieldTheory.Local.AbsoluteRestriction`.

- `unitLinearEquiv` applies the units functor to `closureEquiv K L`,
  writes the units additively, and restricts the integer-linear equivalence
  to `IntegerScalars`. `unitLinearEquiv_apply` identifies its forward map
  with the existing `absoluteRestrictionCoefficients`.
- `unitContinuousEquiv` uses the discrete coefficient topologies to give
  continuity in both directions. `coefficientsInverse` equips its inverse
  with equivariance: apply the injective forward equivalence, use the
  existing coefficient map's equivariance, and cancel the inverse pairs.
- `coefficientsIso` bundles the forward map and this inverse as an
  isomorphism of topological representations. Its inverse identities follow
  pointwise from the linear equivalence. `coefficientsIso_hom` identifies
  its forward morphism exactly. These coefficient declarations require
  finite dimension and the supplied closure embedding, but do not require
  characteristic zero.
- In characteristic zero, `subgroupCoefficientsIso` expresses that same
  isomorphism over `groupEquiv`, with coefficients `A.restrict H.toSubgroup`.
  The equality of the two restricted actions follows from the imported
  actual group map.
- `subgroupCohomologyIso K L q` applies the published
  `Langlands.Continuous.continuousCohomologyIso` to these group and
  coefficient isomorphisms. It identifies continuous cohomology of `H` with
  restricted coefficients with `absoluteCohomology L q`.
  `subgroupCohomologyIso_hom` identifies its forward map with the genuine
  `ContinuousCohomology.map` for `subgroupMap` and the forward coefficient
  morphism.

`continuousRestriction_comp_subgroupCohomologyIso` proves that genuine
subgroup restriction followed by this forward transport is exactly
`absoluteRestriction K L q`. The proof uses the continuous-cohomology
composition identity and the actual inclusion/restriction and coefficient
maps; it assumes no comparison equation.

## Transfer construction and its certificates

Let `T = AbsoluteRestriction.subgroupCohomologyIso K L q`, and let `U`
denote the forgetful functor from `TopModuleCat IntegerScalars` to
`ModuleCat IntegerScalars`. The definition is

```
absoluteCorestriction K L q =
  U.map T.inv ≫ continuousCorestriction A H q.
```

Thus upper-field cohomology is first transported to the cohomology of the
actual open subgroup, then mapped by the published continuous
corestriction. Compactness of the absolute Galois group follows from its
Galois realization in characteristic zero. The subgroup topology and
topological group structure are the inherited ones.

`subgroupCohomologyIso_comp_absoluteCorestriction` proves

```
U.map T.hom ≫ absoluteCorestriction K L q =
  continuousCorestriction A H q.
```

Its proof cancels the two maps of `T` through functoriality and the
isomorphism's inverse identity.
`finiteStageToContinuous_comp_absoluteCorestriction` then gives the exact
finite-stage transfer certificate. For every open normal subgroup `N` of
`G_K` with `hN : N.toSubgroup ≤ H.toSubgroup`, it states

```
finiteStageToContinuous (A.restrict H.toSubgroup)
    (restrictOpenNormal H N) q ≫
  U.map T.hom ≫ absoluteCorestriction K L q =
    finiteCorestriction A.toRep H N hN q ≫
      finiteStageToContinuous A N q.
```

Here the stage coefficients are the actual fixed coefficients, and the
stage maps are genuine inflation maps. The proof first applies the preceding
cancellation identity, then the imported
`finiteStageToContinuous_comp_corestriction`. The continuous transfer itself
is constructed in `Continuous.Corestriction` from finite transfer by colimit
descent and its proved comparison with actual continuous cohomology.

## Source correspondence and scope

This is a derived internal specialization of the published
`AbsoluteRestrictionImage`, `FixedFieldStages`,
`Continuous.EquivalenceTransport`, and `Continuous.Corestriction` APIs.
Worker 42 adapted Worker 134's published `ClosureUnitTransport` inverse
equivariance proof and `ClosureCohomologyTransport` comparison pattern to
arbitrary finite extensions and their actual image subgroup. The generic
cohomology equivalence and continuous transfer are reused by import.

The original source is Jean-Pierre Serre, *Local Fields*, Greenberg
translation (1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Chapter VII, section 7, printed page 119 / PDF page 125 defines
finite-index corestriction in the direction used here and its degree-zero
coset-norm convention. Chapter X, section 3, printed page 154 / PDF page
160 gives continuous cohomology as the inflation-indexed limit with fixed
coefficients. Chapter X, section 4, printed pages 155–156 / PDF pages
161–162 supplies the multiplicative coefficients and compatible field,
group, and coefficient maps. Worker 42 read these original passages and
visually checked page 125. The exact categorical transport and cancellation
certificates are internal constructions, not quotations of a numbered
theorem.

Worker 42 also checked the *Local Fields* entries on PDF pages 2–3 of
`serre-book-corrections-2019`; none changes the cited passages. No
project-specific errata file for the 1979 source was present.

This pair constructs the map and proves its stated intrinsic certificates.
It does not prove independence of different supplied closure embeddings,
transfer transitivity, restriction followed by degree multiplication,
compatibility with local invariants, or any local class-formation existence
theorem. It chooses no invariant or fundamental class and makes no
arithmetic-versus-geometric reciprocity normalization assertion.
