import Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityStatement
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Positive rational proportionality on compact open sets: proof

A compact clopen set stable under a compact open subgroup is a finite disjoint
union of orbits of that subgroup. Refining an orbit of a compact open subgroup
by an open subgroup normal in it multiplies the value of an invariant
distribution by a positive integer. Normal cores and conjugation then compare
every orbit with one fixed reference orbit by a positive rational factor.
-/

noncomputable section

open Topology Pointwise

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uX

namespace HomogeneousPositivity

section Values

variable {X : Type*} [TopologicalSpace X]

open Classical in
/-- The value of a distribution on the indicator of a compact clopen set, and
`0` on every other set. -/
def setValue (D : Distribution X) (S : Set X) : ℂ :=
  if h : IsClopen S ∧ IsCompact S then
    D (Hecke.TestFunction.characteristic h.1 h.2)
  else 0

theorem setValue_eq (D : Distribution X) {S : Set X} (hS : IsClopen S)
    (hc : IsCompact S) :
    setValue D S = D (Hecke.TestFunction.characteristic hS hc) := by
  simp [setValue, hS, hc]

theorem setValue_empty (D : Distribution X) : setValue D ∅ = 0 := by
  rw [setValue_eq D isClopen_empty isCompact_empty]
  have h : Hecke.TestFunction.characteristic (isClopen_empty : IsClopen (∅ : Set X))
      isCompact_empty = 0 := by
    ext x
    simp only [Hecke.TestFunction.characteristic_apply, Set.indicator_empty]
    rfl
  rw [h, map_zero]

theorem setValue_union (D : Distribution X) {S T : Set X}
    (hS : IsClopen S) (hcS : IsCompact S) (hT : IsClopen T) (hcT : IsCompact T)
    (hST : Disjoint S T) :
    setValue D (S ∪ T) = setValue D S + setValue D T := by
  rw [setValue_eq D (hS.union hT) (hcS.union hcT), setValue_eq D hS hcS,
    setValue_eq D hT hcT, ← map_add]
  congr 1
  ext x
  change _ = Hecke.TestFunction.characteristic hS hcS x +
    Hecke.TestFunction.characteristic hT hcT x
  simp only [Hecke.TestFunction.characteristic_apply,
    Set.indicator_union_of_disjoint hST]

/-- Finite additivity of `setValue` over pairwise disjoint compact clopen sets. -/
theorem setValue_biUnion (D : Distribution X) (F : Finset (Set X))
    (hF : ∀ S ∈ F, IsClopen S ∧ IsCompact S)
    (hdisj : (F : Set (Set X)).PairwiseDisjoint id) :
    setValue D (⋃ S ∈ F, S) = ∑ S ∈ F, setValue D S := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [setValue_empty]
  | insert T F hT ih =>
    have hF' : ∀ S ∈ F, IsClopen S ∧ IsCompact S :=
      fun S hS => hF S (Finset.mem_insert_of_mem hS)
    have hdisj' : (F : Set (Set X)).PairwiseDisjoint id :=
      hdisj.subset (by simp)
    have hTcc := hF T (Finset.mem_insert_self T F)
    have hdisjT : Disjoint T (⋃ S ∈ F, S) := by
      refine Set.disjoint_iUnion₂_right.mpr fun S hS => ?_
      have hne : T ≠ S := fun h => hT (h ▸ hS)
      exact hdisj (by simp) (by simp [hS]) hne
    rw [Finset.set_biUnion_insert, Finset.sum_insert hT,
      setValue_union D hTcc.1 hTcc.2
        (isClopen_biUnion_finset fun S hS => (hF' S hS).1)
        (F.isCompact_biUnion fun S hS => (hF' S hS).2) hdisjT,
      ih hF' hdisj']

end Values

section Invariance

variable {G : Type*} {X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

/-- An invariant distribution takes equal values on translates of a compact
clopen set. -/
theorem setValue_smul (D : Distribution X)
    (hD : ∀ g : G, pushforward (Homeomorph.smul g) D = D) (g : G) {S : Set X}
    (hS : IsClopen S) (hc : IsCompact S) :
    setValue D (g • S) = setValue D S := by
  have hgS : IsClopen (g • S) := ⟨hS.isClosed.smul g, hS.isOpen.smul g⟩
  rw [setValue_eq D hgS (hc.smul g), setValue_eq D hS hc]
  conv_lhs => rw [← hD g]
  rw [pushforward_apply]
  congr 1
  ext x
  simp only [Hecke.TestFunction.characteristic_apply,
    Hecke.TestFunction.pullback_apply, Homeomorph.smul_apply, Set.indicator]
  by_cases hx : x ∈ S
  · rw [ite_eq_left (Set.smul_mem_smul_set_iff.mpr hx), ite_eq_left hx]
  · rw [ite_eq_right (mt Set.smul_mem_smul_set_iff.mp hx), ite_eq_right hx]

end Invariance

section Orbits

variable {G : Type*} {X : Type*} [Group G] [MulAction G X]

/-- The orbit `K • x` of a point under a subgroup. -/
def orbitSet (K : Subgroup G) (x : X) : Set X :=
  (fun g : G => g • x) '' (K : Set G)

theorem mem_orbitSet {K : Subgroup G} {x y : X} :
    y ∈ orbitSet K x ↔ ∃ k ∈ K, k • x = y :=
  Iff.rfl

theorem self_mem_orbitSet (K : Subgroup G) (x : X) : x ∈ orbitSet K x :=
  ⟨1, K.one_mem, one_smul G x⟩

theorem orbitSet_eq_of_mem {K : Subgroup G} {x y : X} (hy : y ∈ orbitSet K x) :
    orbitSet K y = orbitSet K x := by
  obtain ⟨k, hk, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m * k, K.mul_mem hm hk, mul_smul m k x⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m * k⁻¹, K.mul_mem hm (K.inv_mem hk), ?_⟩
    simp only [smul_smul, inv_mul_cancel_right]

/-- The conjugate subgroup `g⁻¹ K g`, as the preimage of `K` under `m ↦ g m g⁻¹`. -/
def conjSubgroup (g : G) (K : Subgroup G) : Subgroup G :=
  K.comap (MulAut.conj g).toMonoidHom

theorem mem_conjSubgroup {g m : G} {K : Subgroup G} :
    m ∈ conjSubgroup g K ↔ g * m * g⁻¹ ∈ K := by
  simp [conjSubgroup]

theorem orbitSet_smul (g : G) (K : Subgroup G) (x : X) :
    orbitSet K (g • x) = g • orbitSet (conjSubgroup g K) x := by
  ext z
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(g⁻¹ * k * g) • x, ⟨g⁻¹ * k * g, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_conjSubgroup]
      rw [SetLike.mem_coe] at hk
      simpa [mul_assoc] using hk
    · simp only [smul_smul, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨g * m * g⁻¹, mem_conjSubgroup.mp hm, ?_⟩
    simp only [smul_smul, inv_mul_cancel_right]

theorem conjSubgroup_eq_of_normal {K N : Subgroup G}
    (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) {k : G} (hk : k ∈ K) :
    conjSubgroup k N = N := by
  ext m
  rw [mem_conjSubgroup]
  constructor
  · intro h
    simpa [mul_assoc] using hnorm k⁻¹ (K.inv_mem hk) _ h
  · exact hnorm k hk m

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_conjSubgroup (g : G) {K : Subgroup G} (hK : IsOpen (K : Set G)) :
    IsOpen (conjSubgroup g K : Set G) :=
  hK.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_conjSubgroup (g : G) {K : Subgroup G} (hK : IsCompact (K : Set G)) :
    IsCompact (conjSubgroup g K : Set G) := by
  have h : (conjSubgroup g K : Set G) = conjugationHomeomorph g ⁻¹' (K : Set G) := by
    ext m
    simp [mem_conjSubgroup]
  rw [h, Homeomorph.isCompact_preimage]
  exact hK

/-- Inside a compact open subgroup `K`, every open subgroup contains an open
subgroup of `K` that is normal in `K`. -/
theorem exists_open_normal_le {K H : Subgroup G} (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hHo : IsOpen (H : Set G)) :
    ∃ N : Subgroup G, IsOpen (N : Set G) ∧ N ≤ H ∧ N ≤ K ∧
      ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hW : IsClopen ((Subtype.val : K → G) ⁻¹' (H : Set G)) :=
    ⟨(H.isClosed_of_isOpen hHo).preimage continuous_subtype_val,
      hHo.preimage continuous_subtype_val⟩
  obtain ⟨N₀, hN₀⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW
      (show ((1 : K) : G) ∈ H from H.one_mem)
  refine ⟨N₀.toSubgroup.map K.subtype, ?_, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ N₀.isOpen
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    exact hN₀ hn
  · intro k hk y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr
      ⟨⟨k, hk⟩ * n * ⟨k, hk⟩⁻¹, N₀.isNormal'.conj_mem n hn ⟨k, hk⟩, rfl⟩

variable [TopologicalSpace X]

omit [IsTopologicalGroup G] in
theorem isCompact_orbitSet [ContinuousSMul G X] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (x : X) : IsCompact (orbitSet K x) :=
  hK.image (continuous_id.smul continuous_const)

variable [SigmaCompactSpace G] [BaireSpace X] [T2Space X] [ContinuousSMul G X]
  [MulAction.IsPretransitive G X]

theorem isOpen_orbitSet {K : Subgroup G} (hK : IsOpen (K : Set G)) (x : X) :
    IsOpen (orbitSet K x) :=
  isOpenMap_smul_of_sigmaCompact x _ hK

theorem isClopen_orbitSet {K : Subgroup G} (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (x : X) : IsClopen (orbitSet K x) :=
  ⟨(isCompact_orbitSet hKc x).isClosed, isOpen_orbitSet hKo x⟩

/-- A compact set stable under an open subgroup `N` is a finite disjoint union
of `N`-orbits of its points. -/
theorem exists_orbit_partition {N : Subgroup G} (hNo : IsOpen (N : Set G))
    {U : Set X} (hU : IsCompact U) (hinv : ∀ n ∈ N, ∀ y ∈ U, n • y ∈ U) :
    ∃ F : Finset (Set X), (⋃ S ∈ F, S) = U ∧
      (F : Set (Set X)).PairwiseDisjoint id ∧ ∀ S ∈ F, ∃ y ∈ U, S = orbitSet N y := by
  classical
  obtain ⟨b, hbU, hbfin, hcover⟩ :=
    hU.elim_finite_subcover_image (b := U) (c := orbitSet N)
      (fun y _ => isOpen_orbitSet hNo y)
      (fun y hy => Set.mem_biUnion hy (self_mem_orbitSet N y))
  refine ⟨hbfin.toFinset.image (orbitSet N), ?_, ?_, ?_⟩
  · rw [Finset.set_biUnion_finset_image]
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨n, hn, rfl⟩ := hzy
      exact hinv n hn y (hbU (hbfin.mem_toFinset.mp hy))
    · intro z hz
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hcover hz)
      exact Set.mem_iUnion₂.mpr ⟨y, hbfin.mem_toFinset.mpr hy, hzy⟩
  · intro S hS T hT hST
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS)
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
    refine Set.disjoint_left.mpr fun w hwy hwz => hST ?_
    exact (orbitSet_eq_of_mem hwy).symm.trans (orbitSet_eq_of_mem hwz)
  · intro S hS
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨y, hbU (hbfin.mem_toFinset.mp hy), rfl⟩

/-- Refinement of a compact orbit by an open subgroup normal in the acting
compact subgroup multiplies the invariant value by a positive integer. -/
theorem exists_nat_orbitSet_of_normal (D : Distribution X)
    (hD : ∀ g : G, pushforward (Homeomorph.smul g) D = D) {K N : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hNo : IsOpen (N : Set G)) (hNK : N ≤ K)
    (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (x : X) :
    ∃ n : ℕ, 0 < n ∧ setValue D (orbitSet K x) = n * setValue D (orbitSet N x) := by
  classical
  have hNc : IsCompact (N : Set G) :=
    hKc.of_isClosed_subset (N.isClosed_of_isOpen hNo) hNK
  have hval : ∀ y ∈ orbitSet K x,
      setValue D (orbitSet N y) = setValue D (orbitSet N x) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [orbitSet_smul, conjSubgroup_eq_of_normal hnorm hk,
      setValue_smul D hD k (isClopen_orbitSet hNo hNc x) (isCompact_orbitSet hNc x)]
  have hinv : ∀ n ∈ N, ∀ y ∈ orbitSet K x, n • y ∈ orbitSet K x := by
    rintro n hn _ ⟨k, hk, rfl⟩
    exact ⟨n * k, K.mul_mem (hNK hn) hk, mul_smul n k x⟩
  obtain ⟨F, hFU, hFd, hFo⟩ :=
    exists_orbit_partition hNo (isCompact_orbitSet hKc x) hinv
  have hFcc : ∀ S ∈ F, IsClopen S ∧ IsCompact S := by
    intro S hS
    obtain ⟨y, -, rfl⟩ := hFo S hS
    exact ⟨isClopen_orbitSet hNo hNc y, isCompact_orbitSet hNc y⟩
  have hFv : ∀ S ∈ F, setValue D S = setValue D (orbitSet N x) := by
    intro S hS
    obtain ⟨y, hy, rfl⟩ := hFo S hS
    exact hval y hy
  have hFne : F.Nonempty := by
    have hx := self_mem_orbitSet K x
    rw [← hFU] at hx
    obtain ⟨S, hS, -⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨S, hS⟩
  refine ⟨F.card, hFne.card_pos, ?_⟩
  rw [← hFU, setValue_biUnion D F hFcc hFd, Finset.sum_congr rfl hFv,
    Finset.sum_const, nsmul_eq_mul]

/-- Orbits of two compact open subgroups through the same point have positively
rationally proportional invariant values. -/
theorem exists_rat_orbitSet (D : Distribution X)
    (hD : ∀ g : G, pushforward (Homeomorph.smul g) D = D) {K₁ K₂ : Subgroup G}
    (h₁o : IsOpen (K₁ : Set G)) (h₁c : IsCompact (K₁ : Set G))
    (h₂o : IsOpen (K₂ : Set G)) (h₂c : IsCompact (K₂ : Set G)) (x : X) :
    ∃ q : ℚ, 0 < q ∧
      setValue D (orbitSet K₁ x) = q * setValue D (orbitSet K₂ x) := by
  obtain ⟨N₁, hN₁o, hN₁K₂, hN₁K₁, hN₁n⟩ := exists_open_normal_le h₁o h₁c h₂o
  have hN₁c : IsCompact (N₁ : Set G) :=
    h₁c.of_isClosed_subset (N₁.isClosed_of_isOpen hN₁o) hN₁K₁
  obtain ⟨N₂, hN₂o, hN₂N₁, hN₂K₂, hN₂n⟩ := exists_open_normal_le h₂o h₂c hN₁o
  obtain ⟨a, ha, hva⟩ := exists_nat_orbitSet_of_normal D hD h₁c hN₁o hN₁K₁ hN₁n x
  obtain ⟨b, hb, hvb⟩ := exists_nat_orbitSet_of_normal D hD hN₁c hN₂o hN₂N₁
    (fun k hk n hn => hN₂n k (hN₁K₂ hk) n hn) x
  obtain ⟨c, hc, hvc⟩ := exists_nat_orbitSet_of_normal D hD h₂c hN₂o hN₂K₂ hN₂n x
  refine ⟨(a * b : ℚ) / c, by positivity, ?_⟩
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [hva, hvb, hvc]
  push_cast
  field_simp

/-- Every orbit of a compact open subgroup has invariant value a positive
rational multiple of the value of a fixed reference orbit. -/
theorem exists_rat_orbitSet_reference (D : Distribution X)
    (hD : ∀ g : G, pushforward (Homeomorph.smul g) D = D) (x₀ : X) {K₀ : Subgroup G}
    (h₀o : IsOpen (K₀ : Set G)) (h₀c : IsCompact (K₀ : Set G)) {M : Subgroup G}
    (hMo : IsOpen (M : Set G)) (hMc : IsCompact (M : Set G)) (y : X) :
    ∃ q : ℚ, 0 < q ∧
      setValue D (orbitSet M y) = q * setValue D (orbitSet K₀ x₀) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ y
  have hMo' := isOpen_conjSubgroup g hMo
  have hMc' := isCompact_conjSubgroup g hMc
  rw [orbitSet_smul, setValue_smul D hD g (isClopen_orbitSet hMo' hMc' x₀)
    (isCompact_orbitSet hMc' x₀)]
  exact exists_rat_orbitSet D hD hMo' hMc' h₀o h₀c x₀

end Orbits

section Main

variable {G : Type*} {X : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- A compact open set is stable under some compact open subgroup. -/
theorem exists_compactOpenSubgroup_stable {U : Set X} (hUo : IsOpen U)
    (hUc : IsCompact U) :
    ∃ M : OpenSubgroup G, IsCompact (M : Set G) ∧ ∀ m ∈ M, ∀ y ∈ U, m • y ∈ U := by
  have hev : ∀ᶠ g in 𝓝 (1 : G), ∀ y ∈ U, g • y ∈ U := by
    refine hUc.eventually_forall_of_forall_eventually fun y hy => ?_
    have hU' : U ∈ 𝓝 ((1 : G) • y) := hUo.mem_nhds (by rwa [one_smul])
    exact (continuous_smul.continuousAt (x := ((1 : G), y))).preimage_mem_nhds hU'
  obtain ⟨M, hMc, hMW⟩ := Langlands.compactOpenSubgroupBasis G _ hev
  exact ⟨M, hMc, fun m hm y hy => hMW hm y hy⟩

variable [SigmaCompactSpace G] [BaireSpace X] [T2Space X] [MulAction.IsPretransitive G X]

/-- Every nonempty compact clopen set has invariant value a positive rational
multiple of the value of a fixed reference orbit. -/
theorem exists_rat_setValue (D : Distribution X)
    (hD : ∀ g : G, pushforward (Homeomorph.smul g) D = D) (x₀ : X) {K₀ : Subgroup G}
    (h₀o : IsOpen (K₀ : Set G)) (h₀c : IsCompact (K₀ : Set G)) {U : Set X}
    (hU : IsClopen U) (hUc : IsCompact U) (hne : U.Nonempty) :
    ∃ q : ℚ, 0 < q ∧ setValue D U = q * setValue D (orbitSet K₀ x₀) := by
  classical
  obtain ⟨M, hMc, hMU⟩ := exists_compactOpenSubgroup_stable (G := G) hU.isOpen hUc
  obtain ⟨F, hFU, hFd, hFo⟩ :=
    exists_orbit_partition (N := M.toSubgroup) M.isOpen hUc hMU
  have hFcc : ∀ S ∈ F, IsClopen S ∧ IsCompact S := by
    intro S hS
    obtain ⟨y, -, rfl⟩ := hFo S hS
    exact ⟨isClopen_orbitSet M.isOpen hMc y, isCompact_orbitSet hMc y⟩
  have hq : ∀ S ∈ F, ∃ q : ℚ, 0 < q ∧
      setValue D S = q * setValue D (orbitSet K₀ x₀) := by
    intro S hS
    obtain ⟨y, -, rfl⟩ := hFo S hS
    exact exists_rat_orbitSet_reference D hD x₀ h₀o h₀c M.isOpen hMc y
  choose! q hqpos hqv using hq
  have hFne : F.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    rw [← hFU] at hz
    obtain ⟨S, hS, -⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨S, hS⟩
  refine ⟨∑ S ∈ F, q S, Finset.sum_pos hqpos hFne, ?_⟩
  rw [← hFU, setValue_biUnion D F hFcc hFd, Finset.sum_congr rfl hqv, Rat.cast_sum,
    Finset.sum_mul]

end Main

end HomogeneousPositivity

open HomogeneousPositivity in
/-- Proof of `HomogeneousIndicatorProportionalityStatement`: an invariant
algebraic distribution for a continuous transitive action of a sigma-compact,
locally compact nonarchimedean group takes positively rationally proportional
values on the indicators of any two nonempty compact clopen sets. -/
theorem homogeneousIndicatorProportionality :
    HomogeneousIndicatorProportionalityStatement.{uG, uX} := by
  intro G _ _ _ _ _ X _ _ _ _ _ _ D hD U V hU hcU hV hcV hUne hVne
  have : BaireSpace X := BaireSpace.of_t2Space_locallyCompactSpace
  obtain ⟨K₀, hK₀c, -⟩ :=
    Langlands.compactOpenSubgroupBasis G (Set.univ : Set G) Filter.univ_mem
  obtain ⟨qU, hqU, hvU⟩ :=
    exists_rat_setValue D hD hUne.some K₀.isOpen hK₀c hU hcU hUne
  obtain ⟨qV, hqV, hvV⟩ :=
    exists_rat_setValue D hD hUne.some K₀.isOpen hK₀c hV hcV hVne
  refine ⟨qU / qV, div_pos hqU hqV, ?_⟩
  have hqV' : (qV : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hqV.ne'
  rw [← setValue_eq D hU hcU, ← setValue_eq D hV hcV, hvU, hvV]
  push_cast
  field_simp

end Langlands.HarmonicAnalysis.Distribution
