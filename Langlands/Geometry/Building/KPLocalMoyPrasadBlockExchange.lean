import Langlands.Geometry.Building.KPLocalMoyPrasadRankOne
import Langlands.Geometry.Building.MoyPrasadBlockExchange
import Langlands.Geometry.Building.UnramifiedStabilizerDescent

/-! # Local positive-depth exchange of K-level root blocks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise NNReal
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
    (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

set_option maxHeartbeats 800000 in
/-- The actual torus-depth image normalizes every root-depth subgroup.
Its points have trivial character valuation and therefore fix the apartment. -/
theorem image_le_normalizer_filtration (x : B.Apartment) (r : NNReal)
    (a : characterLattice B.S) (s : ℝ) :
    B.centralizerTorusImage hZ r ≤
      Subgroup.normalizer (B.filtration x a s : Set (rationalPoints H)) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨z, hz, rfl⟩ g hg
  have hzker : z ∈ characterValuationKernel (valuation F) B.centralizer.Z := by
    rw [characterValuationKernel_eq_of_isEquiv (valuation_isEquiv F)]
    exact B.centralizerTorusFiltration_le_characterValuationKernel hZ r hz
  have h := B.apartment.conj_mem_filtration (B.centralizer.toNormalizer z) hg
  rw [B.isOmegaCompatible.smul_eq_self hzker x, CentralizerDatum.toNormalizer,
    weylAction_centralizerToNormalizer, coe_centralizerToNormalizer] at h
  exact h

/-- The same centralizer-depth image normalizes the original two-factor
block subgroup, including its retained doubled-root factor. -/
theorem image_le_normalizer_filtrationBlockSubgroup
    (x : B.Apartment) (r : NNReal) (s : ℝ)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    B.centralizerTorusImage hZ r ≤ Subgroup.normalizer
      (B.filtrationBlockSubgroup (exists_order_eq_one F) x s ha : Set (rationalPoints H)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro z hz g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := hg
  have hv' := Subgroup.le_normalizer_iff.mp (B.image_le_normalizer_filtration hZ x r a s)
    z hz v hv
  have hw' : z * w * z⁻¹ ∈ B.apartment.doubleFiltration x a s := by
    by_cases h2a : 2 • a ∈ relativeRoots B.i
    · rw [B.apartment.doubleFiltration_of_mem x a s h2a] at hw ⊢
      exact Subgroup.le_normalizer_iff.mp
        (B.image_le_normalizer_filtration hZ x r (2 • a) s) z hz w hw
    · rw [B.apartment.doubleFiltration_of_not_mem x a s h2a] at hw ⊢
      rw [Subgroup.mem_bot.mp hw]
      simp
  exact ⟨z * v * z⁻¹, hv', z * w * z⁻¹, hw', by group⟩

/-- Ordinary opposite-root exchange at one positive depth, with the
central factor lowered from depth `2r` to depth `r`. -/
theorem filtration_mul_opposite_subset_image
    (hZcomm : B.LocalTorusCommutatorFriendly hZ) (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) :
    (B.filtration x a r : Set (rationalPoints H)) * B.filtration x (-a) r ⊆
      (B.filtration x (-a) r : Set (rationalPoints H)) *
        (B.centralizerTorusImage hZ r : Set (rationalPoints H)) * B.filtration x a r := by
  refine (B.filtration_mul_opposite_filtration_subset_depth hZ hZcomm x ha r r
    (by positivity)).trans ?_
  exact Set.mul_subset_mul
    (Set.mul_subset_mul subset_rfl (B.centralizerTorusImage_antitone hZ (by simp))) subset_rfl

/-- The doubled positive factor exchanges with the negative ordinary
factor while retaining the original entire positive block. -/
theorem doubleFiltration_mul_opposite_subset_block
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) :
    (B.apartment.doubleFiltration x a r : Set (rationalPoints H)) *
        B.filtration x (-a) r ⊆
      (B.filtration x (-a) r : Set (rationalPoints H)) *
        (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
          B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  change u * v ∈ _
  by_cases h2a : 2 • a ∈ relativeRoots B.i
  · rw [B.apartment.doubleFiltration_of_mem x a r h2a] at hu
    let p := B.doublePositiveMoyPrasadCoordinates hZ hZcomm x ha h2a r r
      (by positivity) ⟨u, hu⟩ ⟨v, hv⟩
    have hz : rationalPoints.map B.centralizer.j
        (p.val.2.1 : rationalPoints B.centralizer.Z) ∈ B.centralizerTorusImage hZ r :=
      Subgroup.mem_map.mpr ⟨p.val.2.1, B.centralizerTorusFiltration_antitone hZ (by simp)
        p.val.2.1.property, rfl⟩
    rw [← p.property]
    exact Set.mul_mem_mul (Set.mul_mem_mul p.val.1.property hz) p.val.2.2.property
  · rw [B.apartment.doubleFiltration_of_not_mem x a r h2a] at hu
    rw [Subgroup.mem_bot.mp hu, one_mul]
    have h1 : (1 : rationalPoints H) ∈
        B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a :=
      (B.filtrationBlockSubgroup (exists_order_eq_one F) x r ha).one_mem
    simpa only [mul_one] using
      Set.mul_mem_mul (Set.mul_mem_mul hv (B.centralizerTorusImage hZ r).one_mem) h1

/-- Inversion of the mixed doubled-positive exchange gives the other
mixed exchange, retaining the original negative block. -/
theorem filtration_mul_oppositeDouble_subset_block
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) :
    (B.filtration x a r : Set (rationalPoints H)) *
        B.apartment.doubleFiltration x (-a) r ⊆
      B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) *
        (B.centralizerTorusImage hZ r : Set (rationalPoints H)) * B.filtration x a r := by
  have hneg : -a ∈ relativeRoots B.i := by
    let : Smooth H.X.hom := B.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  rintro _ ⟨u, hu, v, hv, rfl⟩
  have hinv : u⁻¹ ∈ B.filtration x (-(-a)) r := by
    rw [neg_neg]
    exact (B.filtration x a r).inv_mem hu
  have hex := B.doubleFiltration_mul_opposite_subset_block hZ hZcomm x hneg r hr
    (Set.mul_mem_mul ((B.apartment.doubleFiltration x (-a) r).inv_mem hv) hinv)
  obtain ⟨_, ⟨w, hw, z, hz, rfl⟩, b, hb, heq⟩ := hex
  rw [neg_neg] at hw
  have heq' : b⁻¹ * z⁻¹ * w⁻¹ = u * v := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv heq
  change u * v ∈ _
  rw [← heq']
  exact Set.mul_mem_mul (Set.mul_mem_mul
    ((B.filtrationBlockSubgroup (exists_order_eq_one F) x r hneg).inv_mem hb)
    ((B.centralizerTorusImage hZ r).inv_mem hz)) ((B.filtration x a r).inv_mem hw)

/-- The two doubled factors exchange by ordinary rank-one exchange in
the doubled-root direction; absent factors remain the identity subgroup. -/
theorem doubleFiltration_mul_oppositeDouble_subset_image
    (hZcomm : B.LocalTorusCommutatorFriendly hZ) (x : B.Apartment)
    {a : characterLattice B.S} (r : NNReal) (hr : 0 < r) :
    (B.apartment.doubleFiltration x a r : Set (rationalPoints H)) *
        B.apartment.doubleFiltration x (-a) r ⊆
      (B.apartment.doubleFiltration x (-a) r : Set (rationalPoints H)) *
        (B.centralizerTorusImage hZ r : Set (rationalPoints H)) * B.apartment.doubleFiltration x a r := by
  by_cases h2a : 2 • a ∈ relativeRoots B.i
  · by_cases hneg2a : 2 • -a ∈ relativeRoots B.i
    · rw [B.apartment.doubleFiltration_of_mem x a r h2a,
        B.apartment.doubleFiltration_of_mem x (-a) r hneg2a]
      simpa only [smul_neg] using B.filtration_mul_opposite_subset_image hZ hZcomm x h2a r hr
    · rw [B.apartment.doubleFiltration_of_not_mem x (-a) r hneg2a]
      rintro _ ⟨u, hu, v, hv, rfl⟩
      change u * v ∈ _
      rw [Subgroup.mem_bot.mp hv, mul_one]
      simpa only [one_mul] using Set.mul_mem_mul
        (Set.mul_mem_mul (Subgroup.one_mem (⊥ : Subgroup (rationalPoints H)))
          (B.centralizerTorusImage hZ r).one_mem) hu
  · rw [B.apartment.doubleFiltration_of_not_mem x a r h2a]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    change u * v ∈ _
    rw [Subgroup.mem_bot.mp hu, one_mul]
    simpa only [mul_one] using Set.mul_mem_mul
      (Set.mul_mem_mul hv (B.centralizerTorusImage hZ r).one_mem)
      (Subgroup.one_mem (⊥ : Subgroup (rationalPoints H)))

/-- Full local exchange of the unchanged indivisible-root blocks at
positive depth, including both factors in a nonreduced root system. -/
theorem filtrationBlock_mul_opposite_subset
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) :
    B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a *
        B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) ⊆
      B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) *
        (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
          B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  have hneg : -a ∈ relativeRoots B.i := by
    let : Smooth H.X.hom := B.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      B.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization (UnramifiedClosure F) H B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      x ha
  exact twoFactorBlockExchange
    (B.filtration x a r) (B.apartment.doubleFiltration x a r)
    (B.filtration x (-a) r) (B.apartment.doubleFiltration x (-a) r)
    (B.filtrationBlockSubgroup (exists_order_eq_one F) x r ha) (B.filtrationBlockSubgroup (exists_order_eq_one F) x r hneg)
    (B.centralizerTorusImage hZ r) rfl rfl
    (B.filtration_le_filtrationBlockSubgroup (exists_order_eq_one F) x r ha)
    (B.doubleFiltration_le_filtrationBlockSubgroup (exists_order_eq_one F) x r ha)
    (B.filtration_le_filtrationBlockSubgroup (exists_order_eq_one F) x r hneg)
    (B.image_le_normalizer_filtrationBlockSubgroup hZ x r r ha)
    (B.image_le_normalizer_filtrationBlockSubgroup hZ x r r hneg)
    (B.filtration_mul_opposite_subset_image hZ hZcomm x ha r hr)
    (B.doubleFiltration_mul_opposite_subset_block hZ hZcomm x ha r hr)
    (B.filtration_mul_oppositeDouble_subset_block hZ hZcomm x ha r hr)
    (B.doubleFiltration_mul_oppositeDouble_subset_image hZ hZcomm x r hr)


/-- Actual exchanged coordinates in the original two root blocks and
same-depth torus image. -/
def filtrationBlockExchangeCoordinates
    (hZcomm : B.LocalTorusCommutatorFriendly hZ)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r)
    (u : B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a)
    (v : B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a)) :
    {p : B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) ×
        B.centralizerTorusImage hZ r ×
        B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints H) * (p.2.1 : rationalPoints H) *
        (p.2.2 : rationalPoints H) = (u : rationalPoints H) * (v : rationalPoints H)} := by
  apply Classical.choice
  obtain ⟨_, ⟨v', hv', z, hz, rfl⟩, u', hu', heq⟩ :=
    B.filtrationBlock_mul_opposite_subset hZ hZcomm x ha r hr
      (Set.mul_mem_mul u.property v.property)
  exact ⟨⟨(⟨v', hv'⟩, ⟨z, hz⟩, ⟨u', hu'⟩), heq⟩⟩

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
