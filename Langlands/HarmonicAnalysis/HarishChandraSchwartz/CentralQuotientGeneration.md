# Finite generation of `A / (A ∩ K)` for central subgroups of `G(F)`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientGeneration`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `CentralFourierInversion`: the predicate `HasFGCompactOpenQuotients A` (for every compact open
  subgroup `K` there is a finite `s ⊆ A` with `⟨s⟩ ⊔ (A ∩ K) = A`), the hypothesis of
  `eq_zero_of_forall_centralProjection_eq_zero` (Fourier inversion on `A_G`);
- `Langlands.Representation.Plancherel.RationalNormKernelCentralCover`:
  `Langlands.Plancherel.isCompact_rationalCommonNormKernel_inf_center` (for connected reductive
  `G`, `G¹ ∩ Z(G(F))` is compact in the canonical topology);
- `Langlands.Representation.Plancherel.RationalCharacterTopology`:
  `isClosed_rationalCommonNormKernel`;
- `Langlands.Representation.Plancherel.RationalImageLattice`: `rationalReductiveImage_free_finite`
  (the valuation image of a connected reductive group is a free `ℤ`-module of finite rank); through
  it `RationalCharacterValuation` (`rationalCharacterValuation`, `rationalCommonNormKernel`,
  `rationalCharacterValuation_ker`, `rationalCharacterValuationImage`);
- `Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups`:
  `rationalPoint_isTopologicalGroup`;
- `Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup`:
  `isClosedEmbedding_rationalPointMap` (a closed immersion gives a closed embedding on rational
  points); through it `BruhatTits.localField_t2Space`;
- `Langlands.GroupScheme.Rational.Characters`: `IsSplitComponent` (the Library's Waldspurger
  `A_G`), `IsSplitComponent.isCentralSplitTorus`, `IsCentralSplitTorus.isSplitSubtorus`,
  `IsCentralSplitTorus.range_le_center`, `rationalPoints.map`.

From Mathlib it uses `IsCompact.elim_finite_subcover_image`, `Subgroup.mem_sup_of_normal_right`,
`Subgroup.fg_iff`, `Subgroup.fg_iff_add_fg`, `Submodule.fg_iff_addSubgroup_fg`,
`IsNoetherian.noetherian`, `isNoetherian_of_isNoetherianRing_of_finite`,
`MonoidHom.map_closure`, `Subgroup.subgroupOf_map_subtype` and `IsCompact.of_isClosed_subset`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.
Printed page numbers; the PDF page is the printed page minus 234.

- I.1, printed p. 239 (PDF p. 5): "On pose `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`", and `A_M` is "le
  plus grand tore déployé dans le centre de `M`" (for `M = G`, `A_G`).
- End of VIII.5, printed p. 332 (PDF p. 98): "Par inversion de Fourier sur le groupe `A_G`, il
  existe `χ ∈ Â_G` tel que `p_χ φ ≠ 0`."

The published `CentralFourierInversion` proves that Fourier inversion step for a closed central
subgroup `A` under the hypothesis `HasFGCompactOpenQuotients A`. Waldspurger states no such
finiteness; it is the property of `A_G ≅ (F^×)^r` that makes the inversion a statement about
finitely generated abelian groups. This module proves the hypothesis for every closed central
subgroup of `G(F)`. The statements and proofs are derived for that purpose.
`rationalCommonNormKernel G` is the Library's form of Waldspurger's `G¹` (the common kernel of
the normalized absolute values of the rational characters), and `rationalCharacterValuation G`
is the integer valuation `g ↦ (χ ↦ ord_F χ(g))` whose kernel it is.

## Scope and hypotheses

**Section `Generic`.** `G` is a topological group.

- `hasFGCompactOpenQuotients_of_isCompact`: subgroups `A, A₁` with
  `hAc : A ≤ Subgroup.center G`, `hA₁ : A₁ ≤ A`, `hc : IsCompact (A₁ : Set G)`, a set `s₀ ⊆ A`
  with `hs₀ : s₀.Finite`, and `hgen : Subgroup.closure s₀ ⊔ A₁.subgroupOf A = ⊤`
  (`A = ⟨s₀⟩ A₁`).
- `exists_closure_sup_ker_eq_top`: only the group structure of `G` (the topological instances
  are omitted); a group `M`, `A`, `v : G →* M` and `hfg : (A.map v).FG`.
- `hasFGCompactOpenQuotients_of_map_fg`: a group `M`, `hAc`, `v : G →* M`,
  `hc : IsCompact ((A ⊓ v.ker : Subgroup G) : Set G)` and `hfg : (A.map v).FG`.

**`fg_of_le_of_isNoetherian`** (outside the sections): a commutative group `M`, subgroups
`H ≤ I` (`hHI`), and `[IsNoetherian ℤ (Additive I)]`.

**Section `Rational`.** `F` is a nonarchimedean local field (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`) and `G` a group scheme over `Spec F`; the
rational points `rationalPoints G` carry the canonical topology `rationalPointTopology F G.X`
(set up inside each statement, as in the Library).

- `rationalNormKernelPart G A` (definition): no hypotheses.
- `isCompact_rationalNormKernelPart`: `hG : IsConnectedReductive G`, a subgroup `A` of
  `rationalPoints G` with `A ≤ Subgroup.center (rationalPoints G)` and `IsClosed (A : Set _)`.
- `hasFGCompactOpenQuotients_rationalPoints`: the same hypotheses.
- `hasFGCompactOpenQuotients_splitComponent`: `hG`, a commutative group scheme `A` over `Spec F`
  and `i : A.toGrp ⟶ G` with `hi : IsSplitComponent i`.

## Definitions

- `rationalNormKernelPart G A = A ⊓ rationalCommonNormKernel G`: Waldspurger's `A ∩ G¹`, for
  `A = A_G` the group `A_G¹` of norm-one elements.

## Results

- `hasFGCompactOpenQuotients_of_isCompact`: `HasFGCompactOpenQuotients A`.
- `exists_closure_sup_ker_eq_top`: there is a finite `s₀ ⊆ A` with `⟨s₀⟩ ⊔ (A ∩ ker v) = A`.
- `hasFGCompactOpenQuotients_of_map_fg`: `HasFGCompactOpenQuotients A`.
- `fg_of_le_of_isNoetherian`: `H` is finitely generated.
- `isCompact_rationalNormKernelPart` (**`A ∩ G¹` is compact**).
- `hasFGCompactOpenQuotients_rationalPoints` (**`A / (A ∩ K)` is finitely generated** for every
  compact open `K`): `HasFGCompactOpenQuotients A` for every closed central subgroup `A` of
  `G(F)`, `G` connected reductive.
- `hasFGCompactOpenQuotients_splitComponent` (**Waldspurger's `A_G`**):
  `HasFGCompactOpenQuotients (rationalPoints.map i).range`, the image `A_G(F)` of the rational
  points of a split component.

## Proof notes

1. `hasFGCompactOpenQuotients_of_isCompact`: for a compact open `K`, the open translates `c K`,
   `c ∈ A₁`, cover the compact `A₁`; take a finite subcover `t`
   (`IsCompact.elim_finite_subcover_image`). Every `a ∈ A` is `w b` with `w ∈ ⟨s₀⟩` and
   `b ∈ A₁` (`hgen`, `Subgroup.mem_sup_of_normal_right`; `A₁` is normal in the commutative
   `A`), and `b ∈ c K` for some `c ∈ t`, so `a = (w c)(c⁻¹ b)` with `w c ∈ ⟨s₀ ∪ t⟩` and
   `c⁻¹ b ∈ A ∩ K`.
2. `exists_closure_sup_ker_eq_top`: choose a finite generating set `S` of `v(A)`
   (`Subgroup.fg_iff`) and a preimage in `A` of each element; the chosen set `s₀` satisfies
   `v(⟨s₀⟩) = ⟨S⟩ = v(A)` (`MonoidHom.map_closure`). For `a ∈ A` pick `w ∈ ⟨s₀⟩` with
   `v(w) = v(a)`; then `a = w (w⁻¹ a)` with `w⁻¹ a ∈ A ∩ ker v`.
3. `hasFGCompactOpenQuotients_of_map_fg`: step 2 and step 1 with `A₁ = A ⊓ ker v`.
4. `fg_of_le_of_isNoetherian`: `H ∩ I`, as an additive subgroup of `I`, is a `ℤ`-submodule of the
   Noetherian module `Additive I`, hence finitely generated (`IsNoetherian.noetherian`,
   `Submodule.fg_iff_addSubgroup_fg`, `Subgroup.fg_iff_add_fg`); the images of its generators in
   `M` generate `H` (`Subgroup.subgroupOf_map_subtype`).
5. `isCompact_rationalNormKernelPart`: `G¹ ∩ Z(G(F))` is compact
   (`isCompact_rationalCommonNormKernel_inf_center`). `A ∩ G¹` is closed (`A` closed,
   `isClosed_rationalCommonNormKernel`) and contained in it (`A` central), hence compact.
6. `hasFGCompactOpenQuotients_rationalPoints`: step 3 with `v = rationalCharacterValuation G`,
   whose kernel is `rationalCommonNormKernel G` (`rationalCharacterValuation_ker`). Compactness
   of `A ∩ ker v` is step 5. The image `v(A)` lies in the valuation image
   `rationalCharacterValuationImage G`, which is a finite free `ℤ`-module
   (`rationalReductiveImage_free_finite`), hence Noetherian; step 4 makes `v(A)` finitely
   generated. The topological group structure is `rationalPoint_isTopologicalGroup`.
7. `hasFGCompactOpenQuotients_splitComponent`: step 6 for `A = (rationalPoints.map i).range`. It
   is central by `IsCentralSplitTorus.range_le_center`. It is closed: `i` is a closed subgroup
   (`IsCentralSplitTorus.isSplitSubtorus`, second component, a closed immersion), its source is
   affine (`isAffine_of_isAffineHom`), `F` is Hausdorff (`BruhatTits.localField_t2Space`), and
   `isClosedEmbedding_rationalPointMap` makes `p ↦ p ≫ i` a closed embedding, whose range is the
   image.

## Relation to the Library

- `eq_zero_of_forall_centralProjection_eq_zero` (`CentralFourierInversion`) takes
  `HasFGCompactOpenQuotients A` as a hypothesis; with this module it holds for every closed
  central subgroup of `G(F)`, in particular for the image `A_G(F)` of a split component
  (`hasFGCompactOpenQuotients_splitComponent`).
- Step 5 uses the published compactness `isCompact_rationalCommonNormKernel_inf_center`
  (`RationalNormKernelCentralCover`, from `centralNormKernelCompactness` and
  `rationalCenterComparison`) rather than reproving it.

## Open obligations

For Waldspurger's `A_G`, the other hypotheses of `eq_zero_of_forall_centralProjection_eq_zero`:
a Haar measure on `A_G(F)` (left invariant, positive on open sets, finite on compacts) and the
hypotheses `CentralWeights` for Waldspurger's `Ξ, σ`. The existence of a split component of `G`
is not used here: `i` and `hi` are inputs.
