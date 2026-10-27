# Fundamental-class cup restriction and corestriction laws of a finite class formation

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.ClassFormationTransferLawsStatement`
(module `Langlands.ClassFieldTheory.Local.ClassFormationCupLawsStatement`).
The exact-target theorem is

```
theorem classFormationTransferLaws :
    ClassFormationTransferLawsStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every prime `p` and every raw invariant family `I : InvariantFamily.{u,u} p`
with `I.RelativeClassFormation`, `I.TateTransferCompatibility` holds. Let `F`
and `E` be p-adic fields with `E/F` finite, and let `M` be a common finite
extension with `M/F` and `M/E` Galois. Let `c` and `d` be the fundamental
classes of `M/F` and `M/E` for `I`. Then for every integer `n`

```
Res (c ∪ x) = d ∪ Res x      for x in Ĥⁿ(Gal(M/F), ℤ),
Cor (d ∪ x) = c ∪ Cor x      for x in Ĥⁿ(Gal(M/E), ℤ).
```

Here `∪` is `relativeTateCup` (left cup with a degree-two class, landing in
Tate degree `n + 2` of the units). `Res` and `Cor` are
`relativeTateRestriction` / `relativeTateCorestriction` on units and
`integralTateRestriction` / `integralTateCorestriction` on the trivial integral
module. These are the published all-integer Tate transfers of module
`TateTransfers`.

The module also proves two general facts about the constructed Tate cup
product, and the unscaled local laws for an arbitrary tower `K ⊆ L ⊆ M` with
`M/K` and `M/L` finite. The local laws need no class-formation hypothesis.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):

- Chapter XI, §3 (printed page 168, PDF page 174): the fundamental classes
  satisfy `Res(u_{F/E}) = u_{F/E'}` for `F ⊃ E' ⊃ E` with `F/E` Galois.
- Chapter XI, §3 (printed page 169, PDF page 175): the cup maps
  `θⁿ(F/E) : x ↦ u_{F/E} · x` commute with restriction and corestriction.
  Serre says this follows from the formulas for the `u_{F/E}` and known
  formulas for the cup product. He checks the restriction case with the rule
  `Res(a · b) = Res(a) · Res(b)` (Cartan–Eilenberg, Chapter XII, p. 256).

Serre does not prove the cup formulas. This module uses the published
restriction rule `Langlands.Tate.cup_restriction` and proves the corestriction
rule it needs (the projection formula with the restricted class on the left).
It also proves that the cup product is compatible with reindexing along a
group isomorphism. This is needed because `relativeTateRestriction` lands in
Tate cohomology of `Gal(M/E)`, while the constructed restriction lands in Tate
cohomology of its image subgroup `relativeGaloisSubgroup` of `Gal(M/F)`.

## General lemmas (namespace `Langlands.Tate`)

### Projection formula with the restricted class on the left

Let `H` be a subgroup of a finite group `G`. The Library has only the
right-sided formula `cup_corestriction`, `Cor(a ∪ Res b) = Cor a ∪ b`. This
section proves the left-sided one.

- `restrict_tensorInvariantLeft`: restricting the map `b ↦ a ⊗ b` of a
  `G`-invariant `a` gives the same map for the restricted invariant (`rfl`).
- `tensorCup_corestriction_left_zero`: in first degree `0`,
  `Cor(Res a ∪ b) = a ∪ Cor b`. Proof: `a` is the class of an invariant
  (`zeroClass_surjective`). Then `restrictionZero_zeroClass` and
  `tensorCup_invariantLeft` turn both cups into the map induced by
  `tensorInvariantLeft`, and `corestriction_naturality` together with
  `corestriction_degreeTransport` closes the goal.
- `restricted_tensorRight_shortExact`: restriction preserves short exactness
  of `S ⊗ B` (exactness of `Rep.resFunctor`).
- `tensorCup_corestriction_left_boundary`: for a short complex `S` that is
  split over the scalars, corestricting the cup of a restricted connecting
  image `Res (δ x) ∪ b` gives the degree-transported connecting map
  `tateDeltaTo` of `Cor(Res x ∪ b)`. Proof: `restriction_scalarSplit_delta`
  moves `Res` past `δ`, `tensorCup_delta_first` (for the restricted sequence)
  moves `δ` out of the cup, and `corestriction_deltaTo` moves `Cor` past it.
- `tensorCup_corestriction_left`: `Cor(Res a ∪ b) = a ∪ Cor b` in every
  integer bidegree `(p, q)`. Proof: `tateClass_shift_induction` on the first
  variable. The base case is the degree-zero lemma. In the upward step, both
  sides are connecting images for `shiftUpSequence A`; this uses the boundary
  lemma and `tensorCup_delta_first`. In the downward step, the same identity
  for `shiftDownSequence A` is cancelled by the injective map
  `tensorShiftDownLeftIso` followed by a degree transport.
- `cup_corestriction_left`: the same formula for the cup of any equivariant
  pairing `φ`, via `corestriction_naturality` for `φ.tensorHom`.

### Cup products and reindexing along a group isomorphism

Let `e : G ≃* H` be an isomorphism of finite groups. `reindex e φ n` is the
published map on Tate cohomology induced by `e` and a coefficient map
`φ : Rep.res e.symm A ⟶ B`.

- `reindex_degreeTransport`: reindexing commutes with transport along an
  equality of degrees (`subst`, `rfl`).
- `reindex_eq_map`: `reindex e φ` is identity reindexing followed by the map
  induced by `φ` (from `reindex_naturality`).
- `reindex_id_map`: identity reindexing is natural in the coefficients (from
  `reindex_naturality`).
- `reindexed_shortExact`, `reindexed_tensorLeft_shortExact`: restricting
  along `e.symm` preserves short exactness.
- `reindex_tateDeltaTo`: identity reindexing commutes with `tateDeltaTo`
  (from `reindex_delta`).
- `reindex_tensorInvariantRight`: reindexing the map `a ↦ a ⊗ b` of an
  invariant `b` gives the same map for the reindexed invariant (`rfl`).
- `reindex_tensorCup_zero`: the compatibility in second degree `0`. Proof:
  `zeroClass_surjective`, `reindex_zeroClass`, `tensorCup_invariantRight` on
  both sides, then `reindex_id_map`.
- `reindex_tensorCup_boundary` and `reindexed_tensorCup_boundary`: a cup with
  a connecting image `δ b` in the second variable, before and after
  reindexing, is `(-1)^p` times the connecting image of the cup with `b`
  (`tensorCup_delta_second`, `reindex_delta`, `reindex_tateDeltaTo`).
- `reindexedTensorCoinduced_tate_isZero` and `reindexedTensorShiftDownIso`:
  after reindexing, `A ⊗ coinduced B` still has zero Tate cohomology. So the
  connecting map of the reindexed sequence `A ⊗ shiftDownSequence B` is an
  isomorphism (`tate_delta_isIso`).
- `reindex_tensorCup`: identity reindexing preserves the tensor cup in every
  integer bidegree. Proof: `tateClass_shift_induction` on the second
  variable. The upward step uses the two boundary lemmas for
  `shiftUpSequence B`. The downward step cancels the injective map
  `reindexedTensorShiftDownIso` followed by a degree transport. The sign
  `(-1)^p` occurs on both sides and is removed because
  `(-1)^p · (-1)^p = 1` (`Int.units_mul_self`).
- `Pairing.reindexed`: a `G`-pairing restricted along `e.symm`.
- `reindex_cup`: let `φ : Pairing A B C` over `G` and
  `ψ : Pairing A' B' C'` over `H`, and let `α`, `β`, `γ` be coefficient maps
  from the restrictions along `e.symm`, with
  `γ (φ a b) = ψ (α a) (β b)`. Then
  `reindex e γ (a ∪_φ b) = reindex e α a ∪_ψ reindex e β b` in every integer
  bidegree. Proof: `reindex_eq_map` on all three maps, `reindex_id_map` and
  `reindex_tensorCup` for `φ.reindexed e`, then the published
  `cup_naturality`.

## The unscaled local laws (namespace `Langlands.ClassFieldTheory.Local`)

Let `K ⊆ L ⊆ M` be a tower with `M/K` and `M/L` finite. Write
`H = relativeGaloisSubgroup K L M`, `A = unitsRepresentation K M`, and let `ι`
be the isomorphism `Gal(M/L) ≃* H` used by `relativeSubgroupTateIso` and
`integralSubgroupTateIso`. All finite-type instances are `Fintype.ofFinite`,
as in the published definitions.

- `relativeSubgroupTateIso_relativeRestriction`: for
  `c ∈ H²(Gal(M/K), Mˣ)`, the degree-two subgroup reindexing of the Tate
  class of `relativeRestriction K L M 2 c` is the constructed Tate
  restriction to `H` of the Tate class of `c`. Proof: the published
  `relativeSubgroupTateIso_positive`, `restriction_groupCohomology` and
  `relativeRestriction_comp_subgroupCohomologyIso` in degree two.
- `relativeSubgroupTateIso_relativeTateCup`: for `d ∈ H²(Gal(M/L), Mˣ)`,
  `relativeSubgroupTateIso (n + 2)` sends `d ∪ x` to the cup over `H` of the
  reindexed class of `d` with `integralSubgroupTateIso n x`, for the
  restricted scalar pairing. Proof: unfold to `reindex`, then
  `reindex_degreeTransport` and `reindex_cup` for the two scalar pairings.
  Their compatibility hypothesis holds by `rfl`.
- `relativeTateRestriction_relativeTateCup`:
  `relativeTateRestriction K L M (n + 2) (c ∪ x) =
  relativeRestriction K L M 2 c ∪ integralTateRestriction K L M n x`.
  Proof: apply the injective `relativeSubgroupTateIso (n + 2)`. The two
  lemmas above reduce the right side to a cup over `H` of restricted classes,
  and `restriction_degreeTransport` with the published `cup_restriction`
  gives the left side.
- `relativeTateCorestriction_relativeTateCup`:
  `relativeTateCorestriction K L M (n + 2)
  (relativeRestriction K L M 2 c ∪ x) = c ∪ integralTateCorestriction K L M n x`.
  Proof: unfold the corestriction, rewrite with the same two lemmas, then use
  `corestriction_degreeTransport` and `cup_corestriction_left`.

## The implemented proof of the target

For `I` with `hI : I.RelativeClassFormation`, a tower `F ⊆ E ⊆ M` as above,
and fundamental classes `c` of `M/F` and `d` of `M/E`, the published
`InvariantFamily.fundamentalRestriction_of_relativeClassFormation` (module
`FundamentalConsequencesProof`) gives `relativeRestriction F E M 2 c = d`.
Rewriting `d` with this equation reduces the restriction law to
`relativeTateRestriction_relativeTateCup` and the corestriction law to
`relativeTateCorestriction_relativeTateCup`.

## Notes

- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
- The module imports only published Library modules:
  `ClassFormationCupLawsStatement`, `FundamentalConsequencesProof`,
  `Langlands.Cohomology.Tate.CupTransfer`, `Langlands.Cohomology.Tate.CupProof`,
  `Langlands.Cohomology.Tate.ReindexNaturality` and
  `Langlands.Cohomology.Tate.PositiveRestriction`.
