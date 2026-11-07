# Analytic manifold structures on rational points of smooth algebraic spaces

Author: Worker 105.

This module defines the vocabulary for the analytic-manifold assertion of Proposition 5.4
of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.15. It contains definitions only. The assertion itself is
`AnalyticPointManifoldStatement`, in a separate statement module.

Conrad's sentence reads: "If k is complete and X is smooth then X(k) admits a unique
functorial k-analytic manifold structure which agrees with the scheme case and carries étale
maps to k-analytic local isomorphisms." Here `X` is an algebraic space as in
Proposition 5.4: quasi-separated and locally of finite type over a henselian valued field
`k`.

All names are in the namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. Throughout,
`K : Type u` is a nontrivially normed field. `X(K)` is `RingPoints K X K` with the Library's
étale-chart topology `etaleChartTopology K X`. That is the topology of Proposition 5.4, as
proved in `EtaleChartTopologyAdmissibleProof`.

## Definitions

- `IsSmoothPureDimensional K n X`, for `n : ℕ` and an algebraic space `X` over `Spec K`: `X`
  is quasi-separated, locally separated and locally of finite type over `K`
  (`IsLocallySeparatedLocallyFiniteType K X`). It also has a surjective étale scheme atlas whose
  structure morphism is smooth of relative dimension `n` (`HasAtlasProperty` of Mathlib's
  `SmoothOfRelativeDimension n`).
- `affineSpaceOver K n`, affine `n`-space over `Spec K`: the scheme `ringTest K (MvPolynomial (Fin n) K)`,
  that is, `Spec K[x₁, …, xₙ]` over `Spec K`.
- `affineSpaceCoordinates K n : Aⁿ(K) → (Fin n → K)`: the coordinates of a rational point,
  the values of the variables under the corresponding `K`-algebra map
  `K[x₁, …, xₙ] → K` (`affineRingPointEquiv`).
- `AnalyticPointStructure K`, a structure with one field `chartedSpace`. It is a family of
  Mathlib charted-space structures `ChartedSpace (Fin n → K) (X(K))`, one for every `n` and
  every `X` with `IsSmoothPureDimensional K n X`, each for the étale-chart topology of `X(K)`.
- For `σ : AnalyticPointStructure K`:
  - `σ.IsAnalytic`: each structure is a `K`-analytic manifold structure,
    `IsManifold 𝓘(K, Fin n → K) ω`. Here `ω` is the analytic smoothness class and
    `𝓘(K, Fin n → K)` is the model `Kⁿ` without boundary.
  - `σ.IsFunctorial`: for spaces of dimensions `n` and `m` in the family, every morphism
    `f : X ⟶ Y` induces an analytic map `RingPoints.map f : X(K) → Y(K)`
    (`ContMDiff … ω`).
  - `σ.IsEtaleLocalIso`: for spaces of the same dimension `n`, every étale morphism `f`
    (`IsEtaleMorphism`, Stacks Tag 03FR) induces an analytic local diffeomorphism
    `IsLocalDiffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω (RingPoints.map f)`, that is, a
    `K`-analytic local isomorphism.
  - `σ.AgreesWithAffineSpace`: on affine `n`-space, the coordinate map
    `affineSpaceCoordinates K n` is an analytic diffeomorphism `Aⁿ(K) ≃ Kⁿ`.
  - `σ.IsAdmissible`: the conjunction of the four conditions above.
- `σ.Equivalent τ`: on every space of the family, the identity of `X(K)` is analytic from the
  `σ`-structure to the `τ`-structure and back. So the two structures define the same analytic
  manifold.

## Relation to the source

- **"X smooth".** Mathlib manifolds have a single model space, so the family is indexed by the
  relative dimension `n`. A smooth space over a field is the disjoint union of its open and
  closed subspaces of pure relative dimension `n`, `n ∈ ℕ`. An analytic manifold structure in
  Conrad's sense, whose dimension may vary between components, is therefore the same as a
  structure on each pure-dimensional piece. Pure dimension `n` is expressed on an étale atlas,
  as for the Library's other atlas properties (`SmoothOverBase`).
- **Local separatedness.** The class adds local separatedness, as in the corrected
  Proposition 5.4 (`HenselianSpacePointTopologyStatement`). There, the quotient of `A¹` by
  `x ∼ -x` for `x ≠ 0` (Stacks Project, Example 14.1, Tag 02Z1) is quasi-separated and of
  finite type, and it is smooth because `A¹` is an étale atlas. Its atlas `A¹ → X` is not
  locally injective on `K`-points at `0`, so no structure can carry it to a local
  isomorphism. The assertion is therefore stated for locally separated spaces.
- **"Agrees with the scheme case".** For a smooth scheme of pure dimension `n` the classical
  analytic structure is the one in which étale maps to `Aⁿ` are local analytic
  isomorphisms. Smooth schemes are Zariski-locally étale over affine space. So agreement
  with the scheme case follows from the two conditions `AgreesWithAffineSpace` and
  `IsEtaleLocalIso`, which also pin it down. Conrad's wording is formalized by these two
  conditions.
- **"Unique".** Uniqueness is up to `Equivalent`, that is, up to the identity being an
  analytic diffeomorphism. Two `ChartedSpace` structures with different chosen charts but the
  same maximal atlas define the same manifold.
- **The topology.** Each charted space is over the étale-chart topology. So the analytic
  structure refines the topology of Proposition 5.4, as Conrad's sentence intends.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed p.15,
  Proposition 5.4, third paragraph.
- Stacks Project, Algebraic Spaces, Example 14.1 (Tag 02Z1), in the registered copy
  `stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05`, SHA-256
  `49a75fa582cbeafadb9e1fbbdce130e5b8971322a2c0048d777e8a97f0d0fcf5`. It explains the local
  separatedness hypothesis.
