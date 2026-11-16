import Langlands.Geometry.Building.KPLocalMoyPrasadIntersectionLevi

/-!
# Root intersections of the groups `G(K)_{x,r}` at positive depth

For a closed set `Ψ` of roots in an open half-space, an element of `U_Ψ` lying in the span of
all positive root filtrations at a depth `r ≥ 0` lies in `U_{Ψ,x,r}`. With the sign product
cover this gives `U_Ψ ⊓ G(K)_{x,r} = U_{Ψ,x,r}` for `r > 0`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Every point of a root group lies in some filtration subgroup. -/
theorem exists_mem_filtration (x : D.Apartment) {a : characterLattice S}
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    ∃ s : ℝ, g ∈ D.filtration x a s := by
  by_cases htop : x.val a g = ⊤
  · exact ⟨0, D.mem_filtration.mpr ⟨hg, by rw [htop]; exact le_top⟩⟩
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp htop
    exact ⟨s, D.mem_filtration.mpr ⟨hg, hs.le⟩⟩

/-- Axiom V 3 for the full root groups: for non-opposite roots `a, b`, the commutator
`[U_a(k), U_b(k)]` lies in the span of the root groups `U_{pa+qb}(k)`, `p, q > 0`. -/
theorem rootGroupPoints_commutator_le (x : D.Apartment) {a b : characterLattice S}
    (ha : a ∈ relativeRoots i) (hb : b ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) :
    ⁅rootGroupPoints i a, rootGroupPoints i b⁆ ≤
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q) (_ : p • a + q • b ∈ relativeRoots i),
        rootGroupPoints i (p • a + q • b) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨s, hs⟩ := D.exists_mem_filtration x hg
  obtain ⟨s', hs'⟩ := D.exists_mem_filtration x hh
  have hmem := D.filtration_commutator_le x ha hb hnon s s'
    (Subgroup.commutator_mem_commutator hs hs')
  refine (show (⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
      (_ : p • a + q • b ∈ relativeRoots i),
        D.filtration x (p • a + q • b) (p * s + q * s')) ≤ _ from ?_) hmem
  exact iSup_mono fun p => iSup_mono fun q => iSup_mono fun _ => iSup_mono fun _ =>
    iSup_mono fun _ => D.filtration_le_rootGroupPoints x _ _

/-- **Root intersection inside the positive filtration span.** Let `Ψ` be a set of
`ν`-positive roots closed under positive integral combinations, and `r ≥ 0`. An element of
`U_Ψ` that lies in the span of all `U_{b,x,r}` with `b` positive lies in the span of the
`U_{b,x,r}` with `b ∈ Ψ`. -/
theorem mem_iSup_filtration_of_mem_rootGroups
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) {r : ℝ} (hr : 0 ≤ r) (ν : cocharacterLattice S)
    {Ψ : Set (characterLattice S)} (hΨ : Ψ ⊆ positiveRelativeRoots i ν)
    (hclosed : ∀ b ∈ Ψ, ∀ c ∈ Ψ, ∀ p q : ℕ, 0 < p → 0 < q →
      p • b + q • c ∈ relativeRoots i → p • b + q • c ∈ Ψ)
    {g : rationalPoints G}
    (hgΨ : g ∈ ⨆ b ∈ Ψ, rootGroupPoints i b)
    (hg : g ∈ (⨆ b : positiveRelativeRoots i ν, D.filtration x b r :
        Subgroup (rationalPoints G))) :
    g ∈ ⨆ b ∈ Ψ, D.filtration x b r := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha g hg hg1 => (hrank a ha g hg hg1).1.exists
  have hfin : (RelativeRoot.indivisiblePositiveRoots i ν).Finite :=
    (hS.finite_relativeRoots i).subset (fun _ hb => hb.1.1)
  obtain ⟨n, a, hainj, hrange⟩ := hfin.fin_param
  have ha (j : Fin n) : a j ∈ RelativeRoot.indivisiblePositiveRoots i ν :=
    hrange ▸ Set.mem_range_self j
  let c : Fin (n * 2) → characterLattice S := fun l =>
    if (finProdFinEquiv.symm l).2 = 0 then a (finProdFinEquiv.symm l).1
      else 2 • a (finProdFinEquiv.symm l).1
  let H : Fin (n * 2) → Subgroup (rationalPoints G) := fun l =>
    if c l ∈ Ψ then rootGroupPoints i (c l) else ⊥
  have hHin (l : Fin (n * 2)) (hl : c l ∈ Ψ) : H l = rootGroupPoints i (c l) := ite_eq_left_iff.mpr fun h => absurd hl h
  have hHout (l : Fin (n * 2)) (hl : c l ∉ Ψ) : H l = ⊥ := ite_eq_right_iff.mpr fun h => absurd h hl
  have hc0 (j : Fin n) : c (finProdFinEquiv (j, 0)) = a j := by
    simp only [c, Equiv.symm_apply_apply, ↓reduceIte]
  have hc1 (j : Fin n) : c (finProdFinEquiv (j, 1)) = 2 • a j := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [c, Equiv.symm_apply_apply, ite_eq_right h10]
  have hcover (b : characterLattice S) (hb : b ∈ positiveRelativeRoots i ν) :
      ∃ l, c l = b := by
    obtain ⟨d, hd, hb'⟩ :=
      RelativeRoot.HasOppositeFactorPairs.exists_indivisiblePositiveRoot_eq_or_double
        i hS hE ν hb
    obtain ⟨j, hj⟩ := (show d ∈ Set.range a by rw [hrange]; exact hd)
    rcases hb' with hb' | hb'
    · exact ⟨finProdFinEquiv (j, 0), (hc0 j).trans (hj.trans hb'.symm)⟩
    · exact ⟨finProdFinEquiv (j, 1),
        (hc1 j).trans ((congrArg (2 • ·) hj).trans hb'.symm)⟩
  -- `U_Ψ` is the ordered product of its root groups.
  have hcollect :
      Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
        ((⨆ l, H l : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
      (w := fun l => (latticePairing S (c l) ν).toNat)
    intro j l
    by_cases hj : c j ∈ Ψ
    · by_cases hl : c l ∈ Ψ
      · rw [hHin j hj, hHin l hl]
        refine (D.rootGroupPoints_commutator_le x (hΨ hj).1 (hΨ hl).1
          (positiveRoots_nonopposite ν (hΨ hj) (hΨ hl))).trans ?_
        refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
          iSup_le fun hq => iSup_le fun hroot => ?_
        obtain ⟨hdpos, hheight⟩ :=
          positiveRootCombination_height ν (hΨ hj) (hΨ hl) hp hq hroot
        obtain ⟨m, hm⟩ := hcover _ hdpos
        have hmΨ : c m ∈ Ψ := by
          rw [hm]
          exact hclosed _ hj _ hl p q hp hq hroot
        refine le_iSup_of_le m (le_iSup_of_le
          (show max (latticePairing S (c j) ν).toNat (latticePairing S (c l) ν).toNat <
            (latticePairing S (c m) ν).toNat by rw [hm]; exact hheight) ?_)
        rw [hHin m hmΨ, hm]
      · rw [hHout l hl, Subgroup.commutator_bot_right]
        exact bot_le
    · rw [hHout j hj, Subgroup.commutator_bot_left]
      exact bot_le
  have hpairs := range_orderedSubgroupPairsProduct H
    (fun j => H (finProdFinEquiv (j, 0))) (fun j => H (finProdFinEquiv (j, 1)))
    (fun _ => rfl) (fun _ => rfl)
  have hle : (⨆ b ∈ Ψ, rootGroupPoints i b) ≤ ⨆ l, H l := by
    refine iSup₂_le fun b hb => ?_
    obtain ⟨l, hl⟩ := hcover b (hΨ hb)
    refine le_iSup_of_le l ?_
    rw [hHin l (by rw [hl]; exact hb), hl]
  have hg1 : g ∈ Set.range (fun s : ∀ j, (H (finProdFinEquiv (j, 0)) : Set (rationalPoints G)) *
      (H (finProdFinEquiv (j, 1)) : Set (rationalPoints G)) =>
        (List.ofFn fun j => (s j : rationalPoints G)).prod) := by
    rw [← hpairs, hcollect]
    exact hle hgΨ
  obtain ⟨s, hs⟩ := hg1
  -- The coordinates in the blocks of the positive filtration span.
  have hg2 : g ∈ Set.range (D.orderedFiltrationBlockProduct x (fun _ => r) a) := by
    rw [D.range_orderedPositiveFiltrationBlockProduct_eq_iSup_of_reductive hG hi x r hr ν a
      hrange]
    exact hg
  obtain ⟨t, ht⟩ := hg2
  have hsA (j : Fin n) : (s j : rationalPoints G) ∈ rootGroupPoints i (a j) := by
    obtain ⟨u, hu, v, hv, huv⟩ := (s j).property
    rw [← huv]
    refine Subgroup.mul_mem _ ?_ ?_
    · change u ∈ H (finProdFinEquiv (j, 0)) at hu
      by_cases h : c (finProdFinEquiv (j, 0)) ∈ Ψ
      · rw [hHin _ h, hc0] at hu
        exact hu
      · rw [hHout _ h] at hu
        rw [Subgroup.mem_bot.mp hu]
        exact Subgroup.one_mem _
    · change v ∈ H (finProdFinEquiv (j, 1)) at hv
      by_cases h : c (finProdFinEquiv (j, 1)) ∈ Ψ
      · rw [hHin _ h, hc1] at hv
        exact RelativeRoot.double_subgroup_le i (a j) (Over.mk (𝟙 _)) hv
      · rw [hHout _ h] at hv
        rw [Subgroup.mem_bot.mp hv]
        exact Subgroup.one_mem _
  have hinj := RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
    RelativeRoot.dynamicRootOrderedProduct hG hi ν a hainj hrange (Over.mk (𝟙 _))
  let liftS : ∀ j, rootGroupPoints i (a j) := fun j => ⟨s j, hsA j⟩
  let liftT : ∀ j, rootGroupPoints i (a j) := fun j =>
    ⟨t j, D.filtrationBlock_subset_rootGroupPoints x _ (a j) (t j).property⟩
  have hST : liftS = liftT := by
    apply hinj
    change (List.ofFn fun j => (s j : rationalPoints G)).prod =
      D.orderedFiltrationBlockProduct x (fun _ => r) a t
    exact hs.trans ht.symm
  have hsame (j : Fin n) : (s j : rationalPoints G) = t j :=
    congrArg (fun z => (z j : rationalPoints G)) hST
  -- Each block coordinate lies in the span over `Ψ`.
  set K : Subgroup (rationalPoints G) := ⨆ b ∈ Ψ, D.filtration x b r with hK
  have hfK (b : characterLattice S) (hb : b ∈ Ψ) : D.filtration x b r ≤ K :=
    le_iSup₂_of_le b hb le_rfl
  rw [← ht]
  change (List.ofFn fun j => (t j : rationalPoints G)).prod ∈ K
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  obtain ⟨u, hu, v, hv, huv⟩ := (t j).property
  change u * v = (t j : rationalPoints G) at huv
  change u ∈ D.filtration x (a j) r at hu
  change v ∈ D.doubleFiltration x (a j) r at hv
  rw [← huv]
  by_cases haj : a j ∈ Ψ
  · refine K.mul_mem (hfK _ haj hu) ?_
    by_cases h2 : 2 • a j ∈ relativeRoots i
    · rw [D.doubleFiltration_of_mem x _ _ h2] at hv
      have h2Ψ : 2 • a j ∈ Ψ := by
        have hroot : 1 • a j + 1 • a j ∈ relativeRoots i := by
          rw [one_nsmul, ← two_nsmul]
          exact h2
        have h := hclosed _ haj _ haj 1 1 one_pos one_pos hroot
        rwa [one_nsmul, ← two_nsmul] at h
      exact hfK _ h2Ψ hv
    · rw [D.doubleFiltration_of_not_mem x _ _ h2] at hv
      rw [Subgroup.mem_bot.mp hv]
      exact K.one_mem
  · by_cases h2Ψ : 2 • a j ∈ Ψ
    · have h2 : 2 • a j ∈ relativeRoots i := (hΨ h2Ψ).1
      rw [D.doubleFiltration_of_mem x _ _ h2] at hv
      have hs2 : (s j : rationalPoints G) ∈ rootGroupPoints i (2 • a j) := by
        obtain ⟨u', hu', v', hv', huv'⟩ := (s j).property
        change u' * v' = (s j : rationalPoints G) at huv'
        change u' ∈ H (finProdFinEquiv (j, 0)) at hu'
        change v' ∈ H (finProdFinEquiv (j, 1)) at hv'
        rw [hHout _ (by rw [hc0]; exact haj)] at hu'
        rw [hHin _ (by rw [hc1]; exact h2Ψ), hc1] at hv'
        rw [← huv', Subgroup.mem_bot.mp hu', one_mul]
        exact hv'
      have hu2 : u ∈ rootGroupPoints i (2 • a j) := by
        have hu' : u = (t j : rationalPoints G) * v⁻¹ := by
          rw [← huv, mul_inv_cancel_right]
        rw [hu', ← hsame j]
        exact Subgroup.mul_mem _ hs2 (Subgroup.inv_mem _ (D.mem_filtration.mp hv).1)
      have hu2r : u ∈ D.filtration x (2 • a j) r := by
        refine D.mem_filtration.mpr ⟨hu2, ?_⟩
        rw [x.isValuation.double (a j) (ha j).1.1 h2 u hu2, two_nsmul]
        have h1 := (D.mem_filtration.mp hu).2
        calc (r : WithTop ℝ) ≤ ((r + r : ℝ) : WithTop ℝ) :=
              WithTop.coe_le_coe.mpr (by linarith)
          _ = (r : WithTop ℝ) + r := WithTop.coe_add r r
          _ ≤ x.val (a j) u + x.val (a j) u := add_le_add h1 h1
      exact K.mul_mem (hfK _ h2Ψ hu2r) (hfK _ h2Ψ hv)
    · have hs1 : (s j : rationalPoints G) = 1 := by
        obtain ⟨u', hu', v', hv', huv'⟩ := (s j).property
        change u' * v' = (s j : rationalPoints G) at huv'
        change u' ∈ H (finProdFinEquiv (j, 0)) at hu'
        change v' ∈ H (finProdFinEquiv (j, 1)) at hv'
        rw [hHout _ (by rw [hc0]; exact haj)] at hu'
        rw [hHout _ (by rw [hc1]; exact h2Ψ)] at hv'
        rw [← huv', Subgroup.mem_bot.mp hu', Subgroup.mem_bot.mp hv', one_mul]
      rw [huv, ← hsame j, hs1]
      exact K.one_mem

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

-- Matching the `K`-level filtration span against the apartment lemma over the inertia fixed
-- field unfolds the field instances of `UnramifiedClosure F`; this needs a larger budget.
set_option maxHeartbeats 800000 in
/-- For a closed set `Ψ` of `μ`-positive roots and `r ≥ 0`,
`U_Ψ ∩ U_{Φ⁺(μ),x,r} ⊆ U_{Ψ,x,r}`. -/
theorem mem_rootFiltrationSpan_of_mem_rootGroupSpan (x : B.Apartment) {r : ℝ} (hr : 0 ≤ r)
    (mu : cocharacterLattice B.S) {Ψ : Set (characterLattice B.S)}
    (hΨc : B.IsClosedRootSet Ψ) (hΨ : ∀ b ∈ Ψ, 0 < latticePairing B.S b mu)
    {g : rationalPoints H} (hgΨ : g ∈ B.rootGroupSpan Ψ)
    (hg : g ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r) :
    g ∈ B.rootFiltrationSpan x Ψ r := by
  have hg' : g ∈ (⨆ b : positiveRelativeRoots B.i mu, B.filtration x b r :
      Subgroup (rationalPoints H)) := by
    rw [← rootFiltrationSpan_eq_iSup_subtype]
    exact hg
  have hΨ' : Ψ ⊆ positiveRelativeRoots B.i mu := fun b hb => ⟨hΨc.1 hb, hΨ b hb⟩
  have hgΨ' : g ∈ ⨆ b ∈ Ψ, rootGroupPoints B.i b := by
    unfold rootGroupSpan at hgΨ
    exact hgΨ
  have key := B.apartment.mem_iSup_filtration_of_mem_rootGroups
    B.isConnectedReductive B.isMaximalSplitTorus x hr mu hΨ' hΨc.2 hgΨ' hg'
  unfold rootFiltrationSpan
  exact key

/-- **Clause 4 at positive depth, from the sign product cover.** -/
theorem rootIntersection_of_productCover
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (Ψ : Set (characterLattice B.S)) (ν : V B.S) (hΨc : B.IsClosedRootSet Ψ)
    (hΨ : ∀ b ∈ Ψ, 0 < eval B.S b ν) (x : B.Apartment) {r : ℝ≥0} (hr : 0 < r) :
    B.rootGroupSpan Ψ ⊓ B.moyPrasad hZ x r = B.rootFiltrationSpan x Ψ r := by
  apply le_antisymm
  · rintro g ⟨hgΨ, hg⟩
    obtain ⟨_, mu, hmu, hsign⟩ := B.exists_sign_and_generic ν
    have hΨmu : ∀ b ∈ Ψ, 0 < latticePairing B.S b mu :=
      fun b hb => (hsign b (hΨc.1 hb)).2.2.1 (hΨ b hb)
    obtain ⟨u, hu, z, _, v, hv, huv⟩ :=
      B.exists_mul_of_productCover hZ x r mu (hPC x r hr mu hmu) hg
    have hgplus : g ∈ B.rootGroupSpan (positiveRelativeRoots B.i mu) :=
      B.rootGroupSpan_mono (fun b hb =>
        (show b ∈ positiveRelativeRoots B.i mu from ⟨hΨc.1 hb, hΨmu b hb⟩)) hgΨ
    have h := B.eq_of_mul_eq_mul mu (B.rootFiltrationSpan_le_rootGroupSpan x _ r hu)
      (Subgroup.one_mem _) (B.rootFiltrationSpan_le_rootGroupSpan x _ r hv) hgplus
      (z := z) (z' := 1) (by rw [← huv, map_one, one_mul, one_mul])
    have hgv : g ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r := by
      rw [← h.2.2]
      exact hv
    exact B.mem_rootFiltrationSpan_of_mem_rootGroupSpan x r.coe_nonneg mu hΨc hΨmu hgΨ hgv
  · exact le_inf (B.rootFiltrationSpan_le_rootGroupSpan x Ψ r)
      (B.rootFiltrationSpan_le_moyPrasad hZ x hΨc.1 r)

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
