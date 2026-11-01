# Concrete group data for the positive-rank mixed mirabolic orbit comparisons

Author: Worker 1136 (Lean construction, this text, the import audit and the
informal orientation check). Namespace:
`Langlands.GeneralLinear.Mirabolic.MixedOrbit`.

This pair constructs the concrete group data used in the orbit analysis of
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) 10 (1977). The analysis is in §7.2, printed p.471 (one-based
PDF p.32), for Proposition 4.13(b),(c). The subgroups come from cases (II) and
(III) of §4.12, printed pp.456–458 (PDF pp.17–19). Source ID:
`bernstein-zelevinsky-1977-induced-i`; SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
We read the text of p.471 and also inspected the page image. The task
publisher reports a bounded search that found no BZ77-specific erratum. This
pair reports that search only and does not claim that no errata exist
anywhere.

The pair supplies the following data, and nothing more:

- the representatives;
- their stabilizers in `Q`;
- the coefficient maps;
- the section and stages subgroups;
- the radical intersections, their inclusions and composites;
- continuity and closedness.

It proves no orbit enumeration, double-coset factorization or
stabilizer-to-stages containment. It also proves no character matching,
integral, Haar scaling, induction isomorphism, exactness or derivative
compatibility. No such conclusion is a field or hypothesis of any
declaration here.

## Source content and internal constructions

From the source, BZ77 §7.2 states the following for 4.13(b) in the case
`Φ⁻`. Here `G = P_n` and `M, U` are as in 4.12(II). With `N = P_(n-1)` and
`V = V_n` there are two orbits on `X = P\G`:

- the closed orbit of the point `P e`;
- the open orbit of the point `P w₀⁻¹`, where `w₀` is "the matrix
  corresponding to the cyclic permutation `(k ↦ n-1 ↦ n-2 ↦ … ↦ k)`".

Case (c) is the same with 4.12(III) and the permutation
`((m-1) ↦ n-1 ↦ n-2 ↦ … ↦ m-1)`. Here the source's `k` is its GL rank, which
is our `K = k+1`. Only the representatives and the subgroups come from the
source. The source does not state the orbit claims as formulas that this pair
uses. This pair does not formalize them.

The following are internal constructions, made for the later application of
BZ77 Theorem 5.2:

- the rank transport;
- the generic stabilizer, section, stages and radical-intersection layer;
- the commutative-ring generality.

They are definitions with their own elementary proofs, not claims attributed
to BZ77. The algebra works over any commutative ring `R`. The topology lemmas
are stated for any topological ring. Both specialize literally to `F.Carrier`
with the supplied p-adic topology, as described at the end.

## Ranks, groups and the rank transport

For `k r : ℕ`, set the GL rank `K = k+1`, the source mirabolic rank `m = r+2`
and the total matrix rank `n = k+r+3`. The ambient group is
`G = mirabolic (k+r+2) R`. It consists of actual invertible `n × n` matrices,
indexed by `Fin (k+r+3)`, whose final row is `(0,…,0,1)`. The group
`Q = plusSubgroup (k+r+1) R` is the published `P_(n-1) V_n` inside `P_n`.

The published inducing subgroups `leftSubgroup (k+1) (r+1) R` and
`rightSubgroup (k+1) (r+1) R` live in `mirabolic ((k+1)+(r+1)) R`. Their
projections `leftProjection` and `rightProjection` have targets
`GeneralLinear (k+1) R × mirabolic (r+1) R` (`GL_K × P_m`) and
`mirabolic (r+1) R × GeneralLinear (k+1) R` (`P_m × GL_K`).

- `totalRank_eq k r : k + 1 + (r + 1) = k + r + 2` is the proved arithmetic
  rank equality.
- `rankCast (h : m = n) : mirabolic m R ≃* mirabolic n R` is the actual
  reindexing `reindex (finCongr _)` of the underlying matrix units. It uses no
  `subst` and no cast of types. `rankCast_apply` and `rankCast_symm_apply`
  state the entry formula `(rankCast h g) i j = g (Fin.cast _ i) (Fin.cast _ j)`
  and its inverse. Membership in the mirabolic is proved by reducing to
  `h = rfl`, where the reindexing is the identity (`reindex_finCongr_rfl`).
  `continuous_rankCast` and `continuous_rankCast_symm` hold for any
  topological space `R`.
- `leftInducing k r R := (leftSubgroup (k+1) (r+1) R).comap (rankCast _).symm`
  is the subgroup `H ≤ G`, and `rightInducing` is its case (III) analogue.
  `mem_leftInducing_iff` and `mem_rightInducing_iff` are the defining
  membership.
- `leftInducingHom` and `rightInducingHom` map `H` back to the published
  subgroups. They are `(rankCast _).symm.toMonoidHom.subgroupComap _`, with
  value formula `*_InducingHom_val`.

## Cycles and representatives

All indices are zero-based. For `a ≤ t`, `descendingCycle t a ha` is the
permutation of `Fin (t+2)` with:

- `a ↦ t`;
- `j ↦ j-1` for `a < j ≤ t`;
- every other index fixed, in particular the final index `t+1`.

`descendingCycle_apply_val` and `descendingCycle_symm_apply_val` give the
explicit formulas for the permutation and its inverse.
`descendingCycle_eq_inv_cycleIcc` proves that the permutation is
`(Fin.cycleIcc a t)⁻¹`, the inverse of Mathlib's cycle `(a a+1 … t)`.
`descendingCycle_eq_last_iff` and `descendingCycle_last` show that the final
index is fixed and is the only index sent to the final index.

The source's one-based cycles translate as follows, with `t = k+r+1` (the
zero-based form of one-based `n-1`) in both cases:

| Source | One-based cycle | Zero-based `a` | Lean |
| --- | --- | --- | --- |
| 4.13(b), 4.12(II) | `(K ↦ n-1 ↦ n-2 ↦ … ↦ K)` | `k` | `descendingCycle (k+r+1) k _` |
| 4.13(c), 4.12(III) | `(m-1 ↦ n-1 ↦ n-2 ↦ … ↦ m-1)` | `r` | `descendingCycle (k+r+1) r _` |

Indeed, the zero-based cycle sends `a ↦ t ↦ t-1 ↦ … ↦ a+1 ↦ a`. One-based
`K = k+1` and `m-1 = r+1` are zero-based `k` and `r`. The last total
coordinate `n-1 = k+r+2` (zero-based) is fixed, as in the source.

`cycleElement t a ha R : mirabolic (t+1) R` is the actual permutation matrix
`GeneralLinear.permutation (t+2) R (descendingCycle t a ha)`. The published
convention of `permutation` sends the basis vector `e_j` to `e_(σ j)`, so the
`(i,j)` entry is `1` exactly when `σ j = i` (`cycleElement_entry`). The matrix
lies in the mirabolic because its final row is `e_(t+1)`, which follows from
`descendingCycle_eq_last_iff`. `cycleElement_last_row` and
`cycleElement_last_column` record the final row and column.

`leftCycleElement k r R := cycleElement (k+r+1) k _ R` and
`rightCycleElement k r R := cycleElement (k+r+1) r _ R` are elements of `G`.
They have entry formulas `*_CycleElement_entry` and final-row formulas
`*_CycleElement_last_row`.

The source does not fix a convention for "the matrix corresponding to" a
permutation. We take the published `permutation` matrix of the displayed
cycle itself as `w₀`, so that `w₀ e_j = e_(σ j)`. The other convention, the
transpose, would give `w₀⁻¹`.

The choice matters when the cycle has length at least `3`, that is, when
`r ≥ 1` in case (II) or `k ≥ 1` in case (III). Otherwise the cycle is a
transposition and `w₀ = w₀⁻¹`. Below is an informal check, not formalized
here, that our convention gives the source's open orbit:

- In case (II), every element of `H` preserves `W = span(e_0, …, e_k)`,
  because the lower-left rectangle is zero. So `H g ↦ g⁻¹ W` is well defined
  on `H \ G`. In case (III), `H` preserves `W = span(e_0, …, e_r)`. The
  rectangle with GL rows `r+1, …, k+r+1` and mirabolic columns is zero
  (`mem_rightSubgroup_iff_entry`), and the final row of a mirabolic element
  vanishes in columns `0, …, r`.
- Every `q ∈ Q` preserves the subspace `S` of vectors whose coordinates
  `n-2 = k+r+1` and `n-1` vanish, since rows `n-2` and `n-1` of `q` are
  `e_(n-2) + u e_(n-1)` and `e_(n-1)`. Hence the condition `g⁻¹ W ⊆ S` is
  invariant under right multiplication by `Q`.
- The identity point satisfies `W ⊆ S`. The point `H w₀⁻¹` gives `w₀ W`,
  which is `span(e_0, …, e_(k-1), e_(k+r+1))` in case (II) and
  `span(e_0, …, e_(r-1), e_(k+r+1))` in case (III). It is not contained in
  `S`, so this point is not in the identity orbit.
- With the transposed matrix, the point would give
  `span(e_0, …, e_(k-1), e_(k+1))` or `span(e_0, …, e_(r-1), e_(r+1))`. For
  cycles of length at least `3` this lies in `S`. By the source's two-orbit
  statement, that point would therefore lie in the closed orbit of `P e`.

The two-element families are

- `leftRepresentative k r R := ![leftCycleElement k r R, 1]`;
- `rightRepresentative k r R := ![rightCycleElement k r R, 1]`.

Both have type `Fin 2 → G`, with the cyclic representative at index `0` and
the identity at index `1` (`*_Representative_zero`, `*_Representative_one`).
This is the order intended for the later open-first support filtration. It
asserts no covering, disjointness, openness or closedness.

The published `Geometric.cosetOrbit H Q w` is the range of `q ↦ H w⁻¹ q` in
`H \ G`. So the cyclic family member `w = w₀` is the source's open-orbit
point `P w₀⁻¹`, and `w = 1` is the closed-orbit point `P e`. This orientation
is the one required by the task. We do not state or prove any orbit theorem.

## Stabilizers and coefficient maps

The generic layer is stated for any `t`, any subgroup `H ≤ mirabolic (t+1) R`
and any `w`. Here `stab` denotes `orbitStabilizer H (plusSubgroup t R) w`.

- The stabilizer is `orbitStabilizer H (plusSubgroup t R) w : Subgroup Q`,
  the published `Q ∩ w H w⁻¹`. `mem_orbitStabilizer_iff` gives
  `q ∈ stab ↔ w⁻¹ * q * w ∈ H`.
- `stabilizerToInducing H Q w` is the published inverse conjugation
  `q ↦ w⁻¹ q w`, valued in `H`.
- `sectionSubgroup H w := stab.comap plusSuccessor` is a subgroup of
  `mirabolic t R`. `mem_sectionSubgroup_iff` gives
  `g ∈ _ ↔ w⁻¹ * successor g * w ∈ H`, where `successor g = diag(g,1)`.
- `stagesSubgroup H w := (sectionSubgroup H w).comap plusProjection` is a
  subgroup of `Q`. `mem_stagesSubgroup_iff` gives the formula through
  `successor (plusProjection q)`.
- `radicalIntersection H w := stab.comap plusRadical` is a subgroup of the
  actual radical `radical (t+1) R`, which is `V_(t+2)`.
  `mem_radicalIntersection_iff` gives `u ∈ _ ↔ w⁻¹ * u * w ∈ H`.
- `radicalInclusion H w := plusRadical.subgroupComap _` is the actual
  inclusion of the radical intersection into the stabilizer.
  `radicalInclusion_val` gives its value.

The case-specific declarations take `t = k+r+1`, `H = leftInducing k r R` or
`rightInducing k r R`, and `w` the representative at index `i : Fin 2`:

- `leftStabilizer k r R i` and `rightStabilizer k r R i` are the stabilizers.
- `leftCoefficient k r R i` is
  `leftProjection ∘ leftInducingHom ∘ stabilizerToInducing`, valued in
  `GL_(k+1) × P_(r+2)`. `rightCoefficient` is
  `rightProjection ∘ rightInducingHom ∘ stabilizerToInducing`, valued in
  `P_(r+2) × GL_(k+1)`.
- The entry formulas `*_Coefficient_fst_apply` and `*_Coefficient_snd_apply`
  give each coefficient entry as an entry of `w⁻¹ q w`. The indices are the
  published `leftIndex (k+1) (r+1)` or `rightIndex (k+1) (r+1)` positions,
  composed with `Fin.cast` along `totalRank_eq`. In case (II) the GL factor
  uses `Sum.inl` and the mirabolic factor uses `Sum.inr`. In case (III) the
  mirabolic factor uses `Sum.inl` (the first `r+1` and the final coordinate)
  and the GL factor uses `Sum.inr`.
- `leftSection`, `leftStages`, `leftRadicalIntersection` and
  `leftRadicalInclusion` specialize the generic constructions, and so do their
  `right` versions.
- `leftRadicalCoefficient` and `rightRadicalCoefficient` are the composites
  of the radical inclusion with the coefficient map.

## Continuity and closedness

All topologies are the published subgroup topologies on actual matrix units.

The following hold under `[TopologicalSpace R]`:

- `continuous_plusSuccessor` and `continuous_plusRadical` hold. Each map
  lands in a subtype, so its continuity follows from continuity of
  `successor` or the subtype value map.
- `continuous_radicalInclusion`, `continuous_leftInducingHom`,
  `continuous_rightInducingHom` and both `continuous_*RadicalInclusion` hold.

The following hold under `[IsTopologicalRing R]`:

- `continuous_stabilizerToInducing` follows from continuity of `q ↦ w⁻¹ q w`
  in `G`.
- `continuous_leftCoefficient` and `continuous_rightCoefficient` compose this
  map with `continuous_*InducingHom` and the published
  `continuous_leftProjection` or `continuous_rightProjection`.
- The two radical-coefficient continuity lemmas compose the coefficient maps
  with the inclusions.

`orbitStabilizer_isClosed`, `sectionSubgroup_isClosed`,
`stagesSubgroup_isClosed` and `radicalIntersection_isClosed` hold for any
closed `H`. The stabilizer is the preimage of `H` under the continuous map
`q ↦ w⁻¹ q w`. The other three are preimages of the stabilizer or the section
subgroup under `plusSuccessor`, `plusProjection` (published
`continuous_plusProjection`) and `plusRadical`. These lemmas need no
Hausdorff hypothesis.

`leftInducing_isClosed` and `rightInducing_isClosed` take
`[TopologicalSpace R] [T2Space R]`. They are preimages of the published
`leftSubgroup_isClosed` and `rightSubgroup_isClosed` under `(rankCast _).symm`.
The four closedness statements for each side then follow:
`*_Stabilizer_isClosed`, `*_Section_isClosed`, `*_Stages_isClosed` and
`*_RadicalIntersection_isClosed`.

## The supplied p-adic topology

Section `Padic` keeps the actual hypotheses
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
Every statement there begins `letI := T.topology`.

- `isTopologicalRing_of_topologicalData` shows that `T.topology` makes
  `F.Carrier` a topological ring. The proof installs `T.valuativeRel` and
  `T.localField` and uses instance search, as in the published
  `TopologicalData.generalLinearTopologicalGroup`.
- Hausdorffness is the published `TopologicalData.fieldT2`.
- The literal specializations at `R = F.Carrier` are:
  - `padic_continuous_{left,right}Coefficient`;
  - `padic_continuous_{left,right}RadicalCoefficient`;
  - `padic_continuous_{left,right}RadicalInclusion`;
  - `padic_{left,right}Stabilizer_isClosed`;
  - `padic_{left,right}Section_isClosed`;
  - `padic_{left,right}Stages_isClosed`;
  - `padic_{left,right}RadicalIntersection_isClosed`.

The data constructions themselves apply at `R = F.Carrier` with
`F.Carrier`'s field structure, for example `leftCoefficient k r F.Carrier i`.
No representation carrier, universe, finiteness or irreducibility hypothesis
appears.

All statements hold for every `k r : ℕ`, including `k = 0` and `r = 0`. The
positive ranks `K = k+1 ≥ 1` and `m = r+2 ≥ 2` are built into the indexing.

## Import closure and exclusion audit

The direct imports are:

- `Langlands.Group.GL.MirabolicMixedProductSubgroups`;
- `Langlands.Group.GL.Maps`;
- `Langlands.Group.GL.RankReindex`;
- `Langlands.Group.GL.Padic`;
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`.

The complete transitive project import closure, excluding this module, has
20 modules:

- Matrix and local-field infrastructure:
  - `Langlands.Group.GL.Basic`
  - `Langlands.Group.GL.Maps`
  - `Langlands.Group.GL.Mirabolic`
  - `Langlands.Group.GL.MirabolicMixedProductSubgroups`
  - `Langlands.Group.GL.MirabolicProjection`
  - `Langlands.Group.GL.MirabolicRadical`
  - `Langlands.Group.GL.Padic`
  - `Langlands.Group.GL.RankMaps`
  - `Langlands.Group.GL.RankReindex`
  - `Langlands.Group.GL.UpperUnipotent`
  - `Langlands.LocalField.Canonical`
  - `Langlands.LocalField.Definitions`
  - `Langlands.LocalField.Topology`
- Representation definition modules, imported only through
  `ClosedSubgroupDefinitions`:
  - `Langlands.Representation.Category.Basic`
  - `Langlands.Representation.Filtration.Definitions`
  - `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
  - `Langlands.Representation.Induction.Definitions`
  - `Langlands.Representation.Smooth.Definitions`
  - `Langlands.Representation.Smooth.SmoothPart.Definitions`
  - `Langlands.Representation.Twist.Definitions`

The pair modifies no existing Lean or Markdown file.

From `ClosedSubgroupDefinitions` the Lean uses only the definitions
`orbitStabilizer` and `stabilizerToInducing` and the lemma
`stabilizerToInducing_apply`. These are the subgroup `Q ∩ w H w⁻¹`, the
conjugation homomorphism and its value formula. `cosetOrbit` is cited only in
this Markdown, to fix the orientation. The seven representation modules contain only
definitions: categories of smooth representations, smooth parts, twists,
compact induction, support filtrations and the geometric-lemma data. Their
few theorems are elementary laws of these definitions, and none of them
contains `sorry` or an axiom. The imported modules contain:

- no derivative functor or derivative identity;
- no plus functor or adjunction;
- no BZ77 4.13(d) and no Leibniz or geometric-lemma theorem;
- no finiteness of coinvariants;
- no supercuspidal, segment, socle, head, Jacquet or classification module;
- no proposition statement of any excluded theorem.

Condition by condition against the inherited exclusion union:

- **Plus functor, adjunction, BZ77 4.13(d), general Leibniz theorem.** None
  is imported. The construction laws use only matrix maps. `plusSubgroup`,
  `plusSuccessor`, `plusProjection` and `plusRadical` are published matrix
  infrastructure in `MirabolicProjection`. They carry no plus-functor
  conclusion.
- **Whittaker finiteness.** `Langlands.Whittaker.*Statement` modules, tasks
  5ab445dc, 3ff5c8fb, 62de5903 and the finite-length route of 5428fe2c are
  not imported and not used. No `Whittaker` module is in the closure.
- **Segment, socle and head results.** Tasks 23e98d90, a55c4267, 8fa9f68b,
  7ff2a1e9, 2ae5cbe5, e3634665, cded83f3, 426911b4, 66e3b87c, c84cd52c,
  6780b79c, 23189526, f3a69bc8, 67279e36 and 4ca79bbd are not imported and
  not used. The same holds for `SegmentHeadProductIrreducibility` (8364e73f)
  and the segment Jacquet formulas (ed48ae06, 55ad1e10, b95105c6, 92aea10f).
  No segment, socle or Jacquet module is in the closure.
- **Classification and exhaustion.** Tasks aca8805b, 5eece9e8, 3bfb61fa,
  ebea9a8a, 20e4e1c6, 8252833d, 52e97845, 30341ae4, 1cb45da2, cd8ab97c and
  bf433f0a are not used, and no classification module is imported.
- **Two-supercuspidal results.** Tasks 3c9849a4 and ab61f565,
  `TwoSupercuspidalNonadjacentProductIrreducible` and
  `TwoSupercuspidalProductStructure` are not used.
- **Ze80.** No Ze80 result (§3.5, §9.6, 4.2, 9.3, 9.7) is used.
- **Derivatives.** No BZ77 derivative result is assumed.
- **Pending work.** No pending task, proposition definition or citation is
  used as a proved input. Worker 127 was not contacted.

## Implemented proofs

`descendingCycle` is a `Fin`-valued `Equiv.Perm`. Each of its inverse laws is
an `omega` case split over its defining conditionals.

`descendingCycle_eq_inv_cycleIcc` multiplies by `Fin.cycleIcc`. It splits on
`j < a`, `t < j` and `a ≤ j ≤ t`. It uses `Fin.cycleIcc_of_lt`,
`Fin.cycleIcc_of_gt`, `Fin.cycleIcc_of_le_of_le` and `Fin.val_add_one_of_lt`,
then `omega`.

The membership proof for `cycleElement` rewrites `permutation_entry` and
`descendingCycle_eq_last_iff`.

The two coefficient entry formulas rewrite the published
`stabilizerToInducing_apply` and then hold by definition (`rfl`). The
definitional steps are the published projection entry formulas
(`leftProjection_gl_apply` and its siblings), the rank-cast entry formula and
the `subgroupComap` value.

The continuity and closedness proofs are described above. They compose
published continuous maps and take preimages of the published closed
subgroups. They use no representation theory.

Compilation and staging do not establish acceptance. Publication requires
independent semantic review.
