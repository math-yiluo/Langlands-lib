# Positive rational proportionality on compact open sets: proof

The module
`Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof`
proves
`Langlands.HarmonicAnalysis.Distribution.homogeneousIndicatorProportionality.{uG,uX}`.
Its type is exactly
[`HomogeneousIndicatorProportionalityStatement.{uG,uX}`](HomogeneousPositivityStatement.md).
The module imports that statement module, the published
`Langlands.Topology.CompactOpen.NeighborhoodBasis` (for
`Langlands.compactOpenSubgroupBasis`), and the Mathlib modules
`Mathlib.Topology.Algebra.Group.OpenMapping`,
`Mathlib.Topology.Algebra.ClopenNhdofOne` and
`Mathlib.Topology.Baire.LocallyCompactRegular`. The statement pair and every
pair it imports are unchanged.

The theorem keeps the statement's quantifiers and adds no hypothesis. The
universes `uG` and `uX` stay independent. The distribution `D` is any complex
linear functional on test functions, with no continuity, positivity or
measure assumption. All helper declarations live in the namespace
`Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivity`. Every helper
states only the instances it uses.

## Values on compact clopen sets

`setValue D S` is `D` applied to
`Hecke.TestFunction.characteristic hS hc` when `S` is clopen and compact,
and `0` for any other set. The definition uses `open Classical in` for the
decidability of that condition. `setValue_eq` recovers the characteristic
function value from proofs `hS` and `hc`. Because the test function does not
depend on the chosen proofs, `setValue` only depends on the set.

- `setValue_empty`: `setValue D ∅ = 0`, since the characteristic function of
  `∅` is the zero test function.
- `setValue_union`: for disjoint compact clopen `S` and `T`,
  `setValue D (S ∪ T) = setValue D S + setValue D T`. The characteristic
  function of the union is the sum (`Set.indicator_union_of_disjoint`), and
  `D` is additive.
- `setValue_biUnion`: for a finset `F` of pairwise disjoint compact clopen
  sets, the value of `⋃ S ∈ F, S` is `∑ S ∈ F, setValue D S`. The proof is
  `Finset.induction_on` with `setValue_union`.
- `setValue_smul` (needs only `ContinuousConstSMul G X`): if `D` is invariant,
  that is `pushforward (Homeomorph.smul g) D = D` for all `g`, then
  `setValue D (g • S) = setValue D S` for compact clopen `S`. The proof
  rewrites `D` on the left as its pushforward. With `pushforward_apply` the
  left side becomes `D` of the pullback of the indicator of `g • S` along
  `x ↦ g • x`. That pullback is the indicator of `S` by
  `Set.smul_mem_smul_set_iff`.

## Orbits of subgroups and conjugation

For a subgroup `K` and a point `x`, `orbitSet K x` is the image
`(fun g => g • x) '' K`, and `mem_orbitSet` unfolds it.
`self_mem_orbitSet` shows `x ∈ orbitSet K x`. `orbitSet_eq_of_mem` shows that
`orbitSet K y = orbitSet K x` whenever `y ∈ orbitSet K x`. So two orbits of
the same subgroup are equal or disjoint.

`conjSubgroup g K` is `K.comap (MulAut.conj g).toMonoidHom`. By
`mem_conjSubgroup` its members are the `m` with `g * m * g⁻¹ ∈ K`, so it is
`g⁻¹ K g`.

- `orbitSet_smul`: `orbitSet K (g • x) = g • orbitSet (conjSubgroup g K) x`,
  using `k • g • x = g • ((g⁻¹ * k * g) • x)`.
- `conjSubgroup_eq_of_normal`: if `N` is normalized by every element of `K`
  (`∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N`) and `k ∈ K`, then
  `conjSubgroup k N = N`.

In a topological group:

- `isOpen_conjSubgroup` and `isCompact_conjSubgroup`: conjugates of open,
  respectively compact, subgroups are open, respectively compact. Compactness
  uses the published `conjugationHomeomorph g` from
  `Langlands.HarmonicAnalysis.Distribution.Basic`, whose preimage of `K` is
  `conjSubgroup g K`.
- `exists_open_normal_le`: if `K` is a compact open subgroup and `H` is an
  open subgroup, there is an open subgroup `N` with `N ≤ H`, `N ≤ K`, and `N`
  normalized by every element of `K`. The proof works in the compact group
  `↥K`. There the preimage of `H` is a clopen neighbourhood of `1`, because an
  open subgroup is closed (`Subgroup.isClosed_of_isOpen`). Mathlib's
  `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` gives an
  open normal subgroup `N₀` of `↥K` inside it. `N` is the image
  `N₀.map K.subtype`. It is open in `G` since `K` is open
  (`IsOpen.isOpenMap_subtype_val`), and it is normalized by `K` since `N₀` is
  normal.

Under `ContinuousSMul G X`, `isCompact_orbitSet` shows that the orbit of a
compact subgroup is compact, as the continuous image of `K`.

## Orbits are open, and partitions into orbits

The remaining orbit lemmas assume `[SigmaCompactSpace G] [BaireSpace X]
[T2Space X] [ContinuousSMul G X] [MulAction.IsPretransitive G X]`.

- `isOpen_orbitSet`: the orbit of an open subgroup is open. This is Mathlib's
  open mapping theorem for actions, `isOpenMap_smul_of_sigmaCompact`: for a
  transitive continuous action of a sigma-compact group on a Baire space,
  `g ↦ g • x` is an open map.
- `isClopen_orbitSet`: an orbit of a compact open subgroup is compact and open,
  hence closed in the Hausdorff space `X`, hence clopen.
- `exists_orbit_partition`: if `N` is an open subgroup and `U` is compact with
  `n • y ∈ U` for all `n ∈ N` and `y ∈ U`, then there is a finset `F` of sets
  with `⋃ S ∈ F, S = U`. The members of `F` are pairwise disjoint, and each is
  `orbitSet N y` for some `y ∈ U`. The open orbits `orbitSet N y` with
  `y ∈ U` cover `U`, and `IsCompact.elim_finite_subcover_image` gives a
  finite subfamily. `F` is its image finset. The union lies in `U` by
  stability, and distinct orbits are disjoint by `orbitSet_eq_of_mem`.

## Integer and rational comparison of orbit values

All values below are for an invariant distribution `D`.

- `exists_nat_orbitSet_of_normal`: let `K` be compact, `N ≤ K` open and
  normalized by `K`, and `x : X`. Then
  `setValue D (orbitSet K x) = n * setValue D (orbitSet N x)` for some natural
  number `n > 0`. Here `N` is compact, being closed in `K`. For
  `y = k • x` with `k ∈ K`, `orbitSet_smul` and `conjSubgroup_eq_of_normal`
  give `orbitSet N y = k • orbitSet N x`, so by `setValue_smul` all
  `N`-orbits inside `orbitSet K x` have the same value. The set
  `orbitSet K x` is compact and `N`-stable, so `exists_orbit_partition`
  splits it into a finset `F` of such orbits. `F` is nonempty because it
  covers `x`. Then `setValue_biUnion` gives the value `F.card` times the value
  of `orbitSet N x`.
- `exists_rat_orbitSet`: for compact open subgroups `K₁` and `K₂` and `x : X`
  there is a rational `q > 0` with
  `setValue D (orbitSet K₁ x) = q * setValue D (orbitSet K₂ x)`. Apply
  `exists_open_normal_le` twice. First take `N₁ ≤ K₂`, `N₁ ≤ K₁`, open and
  normalized by `K₁`. Then take `N₂ ≤ N₁`, `N₂ ≤ K₂`, open and normalized by
  `K₂`, hence also by `N₁`. Three uses of `exists_nat_orbitSet_of_normal`,
  for `N₁` in `K₁`, `N₂` in `N₁` and `N₂` in `K₂`, give
  `v(K₁) = a * v(N₁)`, `v(N₁) = b * v(N₂)` and `v(K₂) = c * v(N₂)` with
  positive naturals `a`, `b`, `c`. The ratio is `q = a * b / c`.
- `exists_rat_orbitSet_reference`: fix a point `x₀` and a compact open
  subgroup `K₀`. For every compact open subgroup `M` and every `y : X` there
  is a rational `q > 0` with
  `setValue D (orbitSet M y) = q * setValue D (orbitSet K₀ x₀)`. By
  transitivity `y = g • x₀`. Then `orbitSet_smul` and `setValue_smul` replace
  the orbit by `orbitSet (conjSubgroup g M) x₀`, which is a compact open
  subgroup orbit through `x₀`. Then `exists_rat_orbitSet` applies.

## Arbitrary compact clopen sets

The final section assumes `[NonarchimedeanGroup G] [LocallyCompactSpace G]
[ContinuousSMul G X]`, and then also `[SigmaCompactSpace G] [BaireSpace X]
[T2Space X] [MulAction.IsPretransitive G X]`.

- `exists_compactOpenSubgroup_stable`: every compact open `U ⊆ X` is stable
  under some compact open subgroup `M`, that is `m • y ∈ U` for `m ∈ M` and
  `y ∈ U`. For each `y ∈ U`, continuity of the action at `(1, y)` shows that
  `g • y ∈ U` for `g` near `1`. Compactness of `U`
  (`IsCompact.eventually_forall_of_forall_eventually`) makes this uniform in
  `y ∈ U`. The published `Langlands.compactOpenSubgroupBasis` then gives a
  compact open subgroup inside this neighbourhood of `1`.
- `exists_rat_setValue`: for a nonempty compact clopen `U` there is a rational
  `q > 0` with `setValue D U = q * setValue D (orbitSet K₀ x₀)`. Take `M` from
  `exists_compactOpenSubgroup_stable`, and partition `U` into `M`-orbits by
  `exists_orbit_partition`. Each orbit has a positive rational factor by
  `exists_rat_orbitSet_reference`, and these factors are chosen with
  `choose!`. The partition is nonempty because `U` is nonempty. So by
  `setValue_biUnion` the sum of the factors, which is positive by
  `Finset.sum_pos`, is the required `q`.

## The main theorem

`homogeneousIndicatorProportionality` introduces all data of the statement.
The instance `BaireSpace X` comes from Mathlib's
`BaireSpace.of_t2Space_locallyCompactSpace`, since `X` is Hausdorff and
locally compact. A reference compact open subgroup `K₀` comes from
`Langlands.compactOpenSubgroupBasis` applied to `Set.univ`. The reference
point is `x₀ = hUne.some`. Then `exists_rat_setValue` gives positive
rationals `qU` and `qV` with `setValue D U = qU * r` and
`setValue D V = qV * r`, where `r = setValue D (orbitSet K₀ x₀)`. The
witness is `q = qU / qV > 0`. By `setValue_eq` the required equality
`D(1_U) = q * D(1_V)` becomes `qU * r = (qU / qV) * (qV * r)`, which
`field_simp` closes using `qV ≠ 0`. No value is required to be nonzero, so
the zero distribution is covered.

## Provenance

The statement is an internal derived target, motivated by Bernstein and
Zelevinsky (1976), Example 6.12; see the statement's Markdown. This proof is
internal. It is an elementary orbit-counting argument with compact open
subgroups, normal cores and conjugation, written for this Library, and it
follows no particular printed proof. The analytic inputs are Mathlib's open
mapping theorem for sigma-compact group actions on Baire spaces, its Baire
category theorem for locally compact Hausdorff spaces, and its existence of
an open normal subgroup inside any clopen neighbourhood of the identity of a
compact topological group.
