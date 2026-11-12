# The derivative of the affine roots under V 7

For every nonarchimedean local field `F`, every affine group scheme `G` over `F`
and every `B : ValuationBuildingData G` (universe `u`) whose class `A(S)`
satisfies V 7, this module proves that the derivative set of the affine roots
`Ψ = B.affineRoots` is the whole relative root system:

```text
AffineRootSystem.derivativeRoots B.affineRoots = Set.range (rootForm B.i).
```

This is the field `derivativeRoots_affineRoots` of the published structure
`KPApartmentData.SatisfiesApartmentAxioms` (module `KPApartmentAxioms`), with
the same Lean expression: the derivative part of AS 3 in KP Axiom 4.1.6. The
companion module `ValuationAffineRootSystems` proved only the inclusion `⊆`,
without V 7.

## The proposition

`ValuationBuildingDerivativeAffineRootsStatement : Prop` says: for all `F`, `G`
and `B` as above,

```text
B.apartment.IsTopologyCompatible →
  AffineRootSystem.derivativeRoots B.affineRoots = Set.range (rootForm B.i).
```

`B.apartment.IsTopologyCompatible` is the published V 7 for the class `A(S)` of
`B` (module `KPApartmentAxioms`). It is the `topologyCompatible` field of
`SatisfiesApartmentAxioms`, for the topology `rationalPointTopology F G.X` on
`G(F)`. The proposition keeps V 7 as a hypothesis, so it does not depend on a
proof of V 7. The theorem `valuationBuildingDerivativeAffineRoots` proves it.

## Declarations

In namespace `Langlands.GroupScheme.RelativeRoot`, over an arbitrary field `k`:

* `eq_zero_of_mem_weightSpace_of_mem_positiveWeightSpan_two_smul`: for a split
  torus `S` acting through `i` and `a ≠ 0`, a Lie vector of weight `a` that lies
  in the span of the weight spaces of the positive multiples `n·2a` is zero. The
  weight-space decomposition is internal
  (`isInternal_weightSpace_of_isSplitTorus`), and `a ≠ 2n·a` for `n ≥ 1` because
  the character lattice of a split torus is torsion-free.
* `exists_mem_rootGroupPoints_not_mem_two_smul`: for a connected reductive `G`, a
  maximal split torus `i`, and a relative root `a` with `2a` a root and no
  `n·a` (`n ≥ 3`) a root, some rational point of `U_a` does not lie in
  `U_{2a}`. The proof uses only published group-scheme results. The realizations
  of `U_a` and `U_{2a}` (`rootSubgroupRealization`) have Lie algebras the
  positive weight spans of `a` and `2a`. The quotient `q : U_a → V` by `U_{2a}`
  (`nonempty_doubleRootCommutatorPairing`) has a unique weight vector structure
  `V ≅ G_a^d`, and a Heisenberg normal form (`nonempty_heisenbergNormalForm`)
  supplies a section `sec : V → U_a` of `q`. A nonzero Lie vector of weight `a`
  lies in `Lie U_a`, and by the previous lemma not in `Lie U_{2a}`. So its image
  in `V` is nontrivial, and `d ≥ 1`. The point `x = (1, 0, …, 0) ∈ V(F)` is not
  `1`. Then `sec(x) ∈ U_a(F)`, and `sec(x) ∉ U_{2a}(F)`, since
  `q(sec(x)) = x ≠ 1` and `U_{2a}` is the kernel of `q`.

In namespace `Langlands.Geometry.Building.ValuationBuildingData`, for
`B : ValuationBuildingData G`:

* `filtration_two_smul_le` (V 4): `U_{2a,x,2r} ⊆ U_{a,x,r}` when `2a` is a root.
  It uses `double_subgroup_le` and the axiom `x_{2a}(v) = 2 x_a(v)` of the
  valuation `x` (field `double` of `IsRootDatumValuation`).
* `exists_mul_of_forall_not_mem_affineRoots`: one step of KP Lemma 6.3.9. Assume
  `2a` is a root and no affine root has derivative `a`. Then every
  `u ∈ U_a(F) ∖ {1}` is a product `u' w` with `x_a(u') > x_a(u)`, `u' ∈ U_a(F)`,
  and `w ∈ U_{2a,x,2x_a(u)}`. The reflection functional `ψ` of `u` is not an
  affine root, so the published
  `affineRootGroup_subset_mul_double_of_not_mem_affineRoots` (module
  `HalfWallRootFactorization`) gives `U_ψ ⊆ U_{ψ+} · U_{2ψ}`.
* `exists_mul_inv_mem_filtration_of_forall_not_mem_affineRoots`: the iteration.
  Under the same assumptions, for every `u ∈ U_{a,x,r}` and every `s` there is
  `v ∈ U_{2a,x,2r}` with `u v⁻¹ ∈ U_{a,x,s}`. Suppose not. Then the values
  `x_a(u v⁻¹)` with `v ∈ U_{2a,x,2r}` lie in `[r, s)`. They are values at `x` of
  reflection functionals, so there are only finitely many. This is the
  discreteness of KP Proposition 6.3.7, in the published form
  `finite_bounded_reflectionFunctionals_of_oppositePairs` (module
  `ActualAffineRootLocalFiniteness`). Take `v` with the largest value and apply
  the previous step to `u v⁻¹`. This gives `w` with `w v ∈ U_{2a,x,2r}` and
  `x_a(u (w v)⁻¹) > x_a(u v⁻¹)`, a contradiction.

With V 7, in the section `Topology` (the canonical topology
`rationalPointTopology F G.X` on `G(F)` and the published
`rationalPoint_isTopologicalGroup`):

* `exists_filtration_subset_of_mem_nhds`: every neighbourhood of `1` in `G(F)`
  contains some `U_{a,x,s}`. Its preimage in `U_a(F)` is a neighbourhood of `1`,
  and V 7 says that the `U_{a,x,s}` form a neighbourhood base there.
* `mem_rootGroup_two_smul_of_forall_not_mem_affineRoots`: KP Lemma 6.3.9 under
  V 7. Assume `2a` is a root and no affine root has derivative `a`. Then
  `U_a(F) ⊆ U_{2a}(F)`. Let `u ∈ U_a(F) ∖ {1}` and `r = x_a(u)`. By the
  iteration and the previous lemma, every neighbourhood of `1` contains some
  `v u⁻¹ = (u v⁻¹)⁻¹` with `v ∈ U_{2a,x,2r}`, so `u` lies in the closure of
  `U_{2a,x,2r}` (`mem_closure_iff_nhds_one`). That set is closed by the
  published `isClosed_filtration` (module `KPFiltrationTopology`, which uses
  V 7). So `u ∈ U_{2a,x,2r} ⊆ U_{2a}(F)`.
* `derivativeRoots_affineRoots_of_isTopologyCompatible`: `∇Ψ = Φ`. The inclusion
  `⊆` holds by the definition of `Ψ`. For `⊇`, suppose no affine root has
  derivative `a`.
  - If `2a` is a root, no `n·a` with `n ≥ 3` is a root
    (`RelativeRoot.HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem`). Then
    `exists_mem_rootGroupPoints_not_mem_two_smul` contradicts the previous
    lemma.
  - If `2a` is not a root, take `g ∈ U_a(F)` with finite value
    (`exists_ne_top`) and its reflection functional `ψ`. Then `g ∈ U_ψ ∖ U_{ψ+}`,
    so `U_{ψ+} ≠ U_ψ`. The published `mem_affineRoots_of_not_double_root`
    (module `AffineRootDoubling`) makes `ψ` an affine root with derivative `a`.

The theorem `valuationBuildingDerivativeAffineRoots` applies the last lemma.

## Provenance and scope

Source: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023).

* Axiom 4.1.6, AS 3 (printed pp. 159–160, PDF pp. 190–191) requires `∇Ψ = Φ`.
* Proposition 6.3.8 (printed pp. 219–220, PDF pp. 250–251) assumes V 7. Its
  part (1) is the non-multipliable case. Its part (2) and Corollary 6.3.10 give
  the multipliable case through Lemma 6.3.9, whose proof iterates the
  factorization `U_ψ ⊆ U_{ψ+} · U_{2a}(k)`. It uses Proposition 6.3.7 for
  discreteness and the closedness of `U_{2a}(k)` in `U_a(k)`. KP choose `u` in
  the open set `U_ψ ∖ U_{ψ+}` outside `U_{2a}(k)`, because `U_{2a}` is a proper
  Zariski-closed subgroup of `U_a`.
* Proposition 6.3.13 (printed p. 221, PDF p. 252) collects AS 1–AS 4.

The Lean route differs in two respects. The contradiction is reached in the
closure of the subgroup `U_{2a,x,2r}`, which is closed in `G(F)` under V 7. KP
pass to a limit of a sequence in `U_{2a}(k)`. The element of `U_a(F)` outside
`U_{2a}(F)` comes from the Heisenberg normal form of `U_a` and a Lie-algebra
weight argument; KP use Zariski density. Only V 7 is assumed beyond the fields
of `B`. Not covered here, and still needed for
`ValuationBuildingApartmentAxiomsStatement`: V 7 itself, and the last two
sentences of AS 5.
