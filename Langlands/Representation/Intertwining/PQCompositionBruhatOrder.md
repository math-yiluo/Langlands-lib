# Renard VII.3.5 (i): the Bruhat-order part of the regularity argument

Author: Worker 102. Module `Langlands.Representation.Intertwining.PQCompositionBruhatOrder`,
namespace `Langlands.Aubert.General.RepresentedParabolic` (two lemmas are in
`Langlands.Aubert.General`). Universe parameter `u`.

This module collects the Bruhat-order lemmas used in the proof of the regularity part of
Renard VII.3.5 (i). The proof itself is in `PQCompositionLeviIntersection`, which proves
`PQCompositionBruhatStatement` and `PQCompositionRegularityStatement`. The present module has
an abstract Bruhat-order transfer, a contraction lemma, and the core lemma
`mem_levi_of_mem_mul_of_torus`. It adds no definitions.

## Notation

As in `PQCompositionBruhatStatement`: `P₁ = MN₁`, `P₂ = MN₂`, `P₃ = MN₃` are parabolic
subgroups of `G` with the same Levi embedding `m₀ = l₁ ≫ p₁` of `M`. `P̄ⱼ = MN̄ⱼ` are opposite
parabolics with `Pⱼ(F) ∩ P̄ⱼ(F) = M(F)`. `a : A ⟶ M` is a split component. The root distances
satisfy `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`. The point `z ∈ G(F)` comes with
a maximal split torus `T` of `G` that lies in `M` (`ta`) and in `zMz⁻¹` (`tb`). `Pⱼ(F)` is
`pointImage pⱼ`, and similarly `M(F)`, `Nⱼ(F)`.

## Abstract lemmas

For a group `Γ` (with a topology and continuous multiplication where needed):

- `quotToDoubleCoset_mk_one`: the identity double coset `P · 1 · Q` is the set `P Q`.
- `mk_eq_mk_one_iff`: `PzQ = PQ` as double cosets iff `z ∈ P Q`.
- `mul_subset_of_subset_mul`: if `P₂ ⊆ P₁ P₃` then `P₂ P₃ ⊆ P₁ P₃` and `P₁ P₂ ⊆ P₁ P₃`.
- `commute_of_commutator_eq_one`: let `x` normalize a subgroup `N` and `v ∈ N`. Then
  `x⁻¹ (v⁻¹ x v)` lies in `N`. If that membership forces `x⁻¹ (v⁻¹ x v) = 1`, then `v` and
  `x` commute.
- `IsSemidirectDecomposition.eq_one_of_mem_levi_of_mem_radical` and
  `IsSemidirectDecomposition.exists_mul_eq`, in namespace `Langlands.Aubert.General`: in
  `P = M ⋉ U`, `M ∩ U = 1`, and every element of `P` is `m u`.
- `bruhatLE_mk_one_iff`: `PzQ ≤_{PQ} PQ` (Renard's Bruhat relation, `Geometric.BruhatLE`) iff
  `z` lies in the closure of `P Q`. The closure of `P Q` is stable under left multiplication by
  `P` and right multiplication by `Q`.
- `bruhatLT_mk_one_of_subset_mul`: suppose `P₂ ⊆ P₁ P₃` and `M ≤ P₁ ∩ P₂`, and suppose `z ∈ P₁ P₃`
  implies `z ∈ M`. Then `P₂zP₃ <_{P₂P₃} P₂P₃` implies `P₁zP₃ <_{P₁P₃} P₁P₃`, and
  `P₁zP₂ <_{P₁P₂} P₁P₂` implies `P₁zP₃ <_{P₁P₃} P₁P₃`. The closure part comes from the previous
  inclusions. For strictness: if `z ∈ P₁ P₃`, then `z ∈ M`, so `z ∈ P₂ P₃` and `z ∈ P₁ P₂`.

## Lemmas on rational points

- `eq_one_of_mem_unipotentPoints_of_commute`: over a nonarchimedean local field, a point `u` of
  the dynamic radical `U(χ)(F)` that commutes with every value `χ(t)` is `1`. Proof: choose
  `t` with `tⁿ → 0` (`exists_unit_tendsto_pow_zero`). Then `χ(t)ⁿ u χ(t)⁻ⁿ → 1`
  (`tendsto_cocharPoint_pow_conj`). The sequence is constant equal to `u`, and `G(F)` is
  Hausdorff.
- `conj_cocharPoint_mem_of_torus`: if `T ⊆ M` and `T ⊆ zMz⁻¹` (maps `ta`, `tb`), then for every
  cocharacter `ν` of the central split torus `a` and `s ∈ F^×`,
  `z⁻¹ (ν ≫ a ≫ m₀)(s) z ∈ M(F)`. Proof: `a` factors through `T` via `ta`
  (`IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`). So the value is
  `z · m₀(y) · z⁻¹` for a point `y` built from `tb`
  (`rationalPoints_map_innerIso`).
- `exists_mul_eq_of_secondChart`: for cocharacters `χ`, `ψ` with the same centralizer, every
  `n ∈ U(χ)(F)` is `b c` with `b ∈ U(ψ)(F)` and `c ∈ U(ψ⁻¹)(F) ∩ U(χ)(F)`. This is the Library
  chart `OppositeCharts.secondChart`.

## Core lemma `mem_levi_of_mem_mul_of_torus`

If `z ∈ P₁(F) P₃(F)` and `T ⊆ M ∩ zMz⁻¹` as above, then `z ∈ M(F)`. (Only the pairs `(P₁, P̄₁)`
and `(P₃, P̄₃)` are used, not the root hypotheses.)

Proof. `exists_oppositePair_cocharacter` (from `PQCompositionProductDecomposition`) is applied
three times: to `(P₁, P̄₁)`, giving `λ₁`; to `(P₃, P̄₃)`, giving `λ₃`; and to the reversed pair
`(P̄₃, P₃)`, giving `λ̄`. So `N₁(F) = U(λ₁)(F)`, `N₃(F) = U(λ₃)(F)`, `N̄₃(F) = U(λ̄)(F)`,
`N₃(F) = U(-λ̄)(F)`, and `M = Z(λ₁) = Z(λ₃) = Z(λ̄)`.

1. Write `z = m n y` with `m ∈ M(F)`, `n ∈ N₁(F)`, `y ∈ P₃(F)`. The chart for `(λ₁, λ̄)` gives
   `n = b c` with `b ∈ N̄₃(F)` and `c ∈ N₃(F)`. So `z = v w` with `v = m b m⁻¹ ∈ N̄₃(F)` (`M`
   normalizes `N̄₃`) and `w = m c y ∈ P₃(F)`.
2. `v = 1`. Let `x = λ̄(s) ∈ M(F)`. By `conj_cocharPoint_mem_of_torus`, `z⁻¹ x z ∈ M(F)`. So
   `v⁻¹ x v = w (z⁻¹ x z) w⁻¹ ∈ P₃(F)`. The commutator `x⁻¹ (v⁻¹ x v)` therefore lies in `P₃(F)`,
   and if it lies in `N̄₃(F)`, it lies in `P₃(F) ∩ P̄₃(F) = M(F)`. Since `M(F) ∩ N̄₃(F) = 1`, it is
   `1` (`commute_of_commutator_eq_one`). Hence `v` commutes with every `λ̄(s)`, and
   `eq_one_of_mem_unipotentPoints_of_commute` gives `v = 1`.
3. Now `z = w = m' u` with `m' ∈ M(F)` and `u ∈ N₃(F)`. Let `x = λ₃(s)`. It commutes with `m'`
   (`commute_cocharPoint`, since `m' ∈ Z(λ₃)`), so `u⁻¹ x u = z⁻¹ x z ∈ M(F)`. The commutator
   lies in `M(F) ∩ N₃(F) = 1`. So `u` commutes with every `λ₃(s)` and `u = 1`. Hence
   `z = m' ∈ M(F)`.

## Use

`pqCompositionBruhat` (in `PQCompositionLeviIntersection`) combines these lemmas. It proves
`P₂(F) ⊆ P₁(F) P₃(F)` and applies `bruhatLT_mk_one_of_subset_mul` with the core lemma. This gives
item 1 and the Bruhat part of item 2 of `PQCompositionBruhatStatement`.

## Relation to Renard

Renard (printed p.237 / PDF p.243) shows `w̄ <_{P₂P₃} 1̄ ⇒ w̄ <_{P₁P₃} 1̄` from
`P₁ \overline{P₂P₃} ⊂ \overline{P₁P₂P₃} = \overline{P₁P₃}`. He leaves strictness implicit in
his Weyl-group indexing. The inclusion `P₂ ⊆ P₁P₃` used here is his `P₁P₂P₃ = P₁P₃`. The core
lemma, which handles strictness for torus-adapted representatives, is a derived argument and is
not in Renard. It is the usual commutator-and-contraction argument.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Proposition VII.3.5 (i),
proof, printed pp.237–238 / PDF pp.243–244.
