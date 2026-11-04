# Conditional cocompactness of derived points in the rational norm kernel

Author: Worker 723.

This is internal infrastructure for task `bbd4ee2c`. It derives the published target
`CentralDerivedNormKernelCocompactnessStatement.{u}` from three other published
propositions. All three remain explicit inputs of
`centralDerivedNormKernelCocompactness_of_premises`. The module does **not** prove the
target unconditionally, and it proves none of the three inputs. Following the Library's
convention for such reductions, the final assembly is a proposition-valued `def` under
`set_option linter.defProp false`; the other results are theorems.

## Inputs

1. `ReductiveCentralTorusSurjectivityStatement.{u}`
   (`Langlands.GroupScheme.Reductive.CentralTorusSurjectivityStatement`; proof task
   `5c7bdf70`). For a connected reductive `M` and an actual derived-subgroup inclusion
   `d : D ⟶ M`, it supplies a closed central torus `i : Z ⟶ M` such that the
   multiplication map `subgroupProductMap i d` is surjective on underlying schemes.
2. `Plancherel.TorusNormKernelCompactnessStatement.{u}`
   (`Langlands.Representation.Plancherel.TorusNormKernelCompactnessStatement`; proof
   task `2c45b1e1`). For every affine, locally finite type torus `T` over a
   nonarchimedean local field, `rationalCommonNormKernel T` is compact.
3. `SmoothRationalPointOpenMapStatement.{u}`
   (`Langlands.AlgebraicGeometry.PointTopology.SmoothOpenMapStatement`, by Worker 1505).
   A smooth morphism of affine schemes over the local field induces an open map
   between the canonical rational-point topologies.

All other ingredients are proved Library results: `derivedSubgroupRepresentability`,
`derivedSubgroupSmoothness`, `normalSubgroupQuotient`,
`RelativeRoot.IsFppfQuotient.smooth_of_smooth_kernel`,
`torusImageClosedTorusStatement`, `isIso_of_isClosedImmersion_of_surjective`,
`isReduced_of_smooth_over_field`, `IsTorus.of_iso`,
`IsDerivedSubgroup.characterRestrict_eq_zero`,
`Plancherel.isClosed_rationalCommonNormKernel`, `rationalPoint_isTopologicalGroup` and
`rationalPoint_locallyCompactSpace`. The topological core is
`compactSpace_quotient_subgroupOf_of_isOpenMap` from `OpenHomCocompactness`.

## Results

### `compactSpace_normKernel_quotient_of_isOpenMap`

Let `M` and `Q` be group schemes over `Spec F` with affine, locally finite type
underlying schemes. Let `q : M ⟶ Q` be a homomorphism and `H` a subgroup of
`rationalPoints M`. Assume:

- every rational point killed by `rationalPoints.map q` is a derived point, i.e. lies
  in `(derivedSubgroup M).carrier (Over.mk (𝟙 _))`;
- the derived points lie in `rationalCommonNormKernel M` and in `H`;
- `rationalPoints.map q` is open for the two canonical point topologies;
- `rationalCommonNormKernel Q` is compact.

Then `rationalCommonNormKernel M ⧸ H.subgroupOf (rationalCommonNormKernel M)` is compact.

The proof applies the topological core lemma with `G = rationalPoints M`,
`T = rationalPoints Q`, `K = rationalCommonNormKernel M` and `C₀ = rationalCommonNormKernel Q`.
`G` is a topological group and locally compact, and `T` is a topological group, by the
Library's point-topology results; `F` is Hausdorff by `localField_t2Space`. `K` is
closed. The kernel conditions are the first two hypotheses. `q` maps `K` into `C₀`
because for each rational character `χ` of `Q`, its restriction `χ ∘ q` is a rational
character of `M`, and `rationalCharacterEval_characterRestrict` turns
`|χ(q x)| = |(χ ∘ q)(x)|` into the norm-kernel condition for `x`. Continuity of
`rationalPoints.map q` is not needed.

### `derivedPoints_le_rationalCommonNormKernel`

For `M` with `IsAffineHom M.X.hom` and `LocallyOfFiniteType M.X.hom`, every rational
point of the scheme-theoretic derived subgroup lies in the norm kernel. The proof takes
an actual derived-subgroup inclusion `d` from `derivedSubgroupRepresentability`, writes
the point as `y ≫ d`, and uses that every rational character restricts to zero on `d`
(`IsDerivedSubgroup.characterRestrict_eq_zero`). This is the actual-point version of
Renard's inclusion `𝒟G ⊆ ⁰G` (V.2.3, Proposition). The target statement does not assume
this inclusion, so it is proved here.

### `isTorus_of_isFppfQuotient_derivedSubgroup`

Assume input 1. Let `M` be connected reductive over a field `k`, `d` an actual
derived-subgroup inclusion, and `q : M ⟶ Q` an fppf quotient by `derivedSubgroup M`
in the sense of `RelativeRoot.IsFppfQuotient`, with `Q` smooth and affine. Then `Q` is
a torus. Proof:

1. `d ≫ q` is trivial, because `d`, viewed as a point of `M`, is a derived point and the
   fppf kernel of `q` is the derived subgroup (`mem_range_kernelι_iff`).
2. Input 1 gives a central torus `i : Z ⟶ M`. Composing `q` with
   `subgroupProductMap i d = (fst ≫ i) * (snd ≫ d)` gives `fst ≫ (i ≫ q)`. Since `q` is
   surjective on schemes, `i ≫ q` is surjective on underlying schemes.
3. `torusImageClosedTorusStatement` factors `i ≫ q = f ≫ j` through a closed torus
   `j : Z' ⟶ Q`. Then `j` is surjective as well.
4. `Q` is smooth over a field, hence reduced. A surjective closed immersion onto a
   reduced scheme is an isomorphism, and an isomorphism of underlying schemes reflects
   to an isomorphism of group schemes. `IsTorus.of_iso` transports the torus property
   from `Z'` to `Q`.

This is the scheme-theoretic form of the identity
`G/𝒟G ≃ R(G)/(R(G) ∩ 𝒟G)` with `R(G)` a central torus (Renard V.2.2), from which Renard
concludes in V.2.6 that `G/𝒟G` is a torus. Milne proves the same statement as
Proposition 12.46(b), applied with the radical as central torus, as in his proof of
Proposition 21.60.

### `centralDerivedNormKernelCocompactness_of_premises`

From inputs 1–3 it proves `CentralDerivedNormKernelCocompactnessStatement.{u}`. For a
nonarchimedean local field `F` and a connected reductive `M`:

1. `derivedSubgroupRepresentability` and `derivedSubgroupSmoothness` give a smooth
   affine derived-subgroup inclusion `d : D ⟶ M`. It is closed and normal.
2. `normalSubgroupQuotient` gives a smooth affine `Q` and an fppf quotient `q : M ⟶ Q`
   by the range of `d`, which equals `derivedSubgroup M`.
3. `Q` is a torus by the previous theorem. `q` is smooth by `smooth_of_smooth_kernel`,
   since its kernel `D` is smooth and `q` is quasi-compact between affine schemes.
4. Input 3, applied to the underlying morphism `q.hom.hom`, makes `rationalPoints.map q`
   open. That map is `y ↦ y ≫ q.hom.hom` by definition (`rationalPoints.map_apply`).
   Input 2 makes `rationalCommonNormKernel Q` compact. The kernel of
   `rationalPoints.map q` consists of derived points, by the fppf kernel condition.
5. `compactSpace_normKernel_quotient_of_isOpenMap` with
   `H = (schemeCenterPoints M ⊓ K) ⊔ D` gives the target. `D ≤ H` holds by
   `le_sup_right`. The central factor `schemeCenterPoints M ⊓ K` plays no further role:
   compactness modulo the smaller subgroup `D` already implies compactness modulo `H`.

## Group and topology comparisons

Every group here is an actual point group `rationalPoints M = (Over.mk (𝟙 _) ⟶ M.X)`.
The topology is `rationalPointTopology F M.X`, exactly as installed by the target, with
the inherited subgroup and quotient topologies on `K ⧸ H.subgroupOf K`. No surjectivity
of `rationalPoints.map q`, finiteness of index, or isogeny image on rational points is
used. Only openness of the point map is used, so the argument applies equally in
positive characteristic. This matters because, as Renard's 2010 errata record, images of
inseparable isogenies on rational points need not have finite index there.

## Sources

- Renard, *Représentations des groupes réductifs p-adiques*, French version dated
  9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: V.2.2 (printed
  p.105 / PDF p.111) for `G/𝒟G ≃ R(G)/(R(G)∩𝒟G)`; V.2.3 Proposition (printed p.106 /
  PDF p.112) for `𝒟G ⊆ ⁰G`; V.2.6 Lemma proof (printed p.108 / PDF p.114) for
  "`G' = G/𝒟G` is a torus".
- Milne, *Algebraic Groups* (2022 corrected reprint), `milne-2022-algebraic-groups`,
  SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`:
  Proposition 12.46(b) (printed p.246 / PDF p.257) and the proof of Proposition 21.60
  (printed p.442 / PDF p.453).
- Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
  `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`: the discussion
  before Theorem 4.5 (PDF p.11) that a smooth morphism induces an open map on points
  over a complete valued field. This is the content of input 3.

The route through an open quotient map onto a torus is this module's own derivation.
Renard's text treats the corresponding cocompactness through the radical and derived
points without the scheme-theoretic quotient.
