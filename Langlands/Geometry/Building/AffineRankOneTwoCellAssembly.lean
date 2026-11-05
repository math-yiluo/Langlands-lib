import Langlands.Geometry.Building.AffineRankOneTwoCellStatement
import Langlands.Geometry.Building.CentralizerZeroRootConjugation
import Langlands.Geometry.Building.RootReflectionSquare
import Langlands.Group.FilteredRankOneTwoCell

/-! # Assembly of the actual filtered rank-one cells -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

private theorem inv_conj_mem_of_map_conj_eq
    {H : Type*} [Group H] {U V : Subgroup H} {m a : H}
    (h : U.map (MulAut.conj m).toMonoidHom = V) (ha : a ∈ V) :
    m⁻¹ * a * m ∈ U := by
  rw [← h] at ha
  simpa only [MulAut.conj_symm_apply] using Subgroup.mem_map_equiv.mp ha

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    {u : rationalPoints G} {p : rationalPoints G × rationalPoints G}

/-- Actual factorization supplies a pair for some element at a strict filtration jump. -/
theorem exists_pair_at_affineRootGroup_jump
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    ∃ m : normalizerPoints P.i,
      ∃ u ∈ P.affineRootGroup α ψ, u ∉ P.apartment.affineRootGroupPlus α ψ ∧
        ∃ p, ∃ hp : RelativeRoot.IsOppositeFactorPair P.i
          (α : characterLattice P.S) u p, m = P.reflectionElement hp := by
  classical
  have hnot : ¬ (P.affineRootGroup α ψ : Set (rationalPoints G)) ⊆
      P.apartment.affineRootGroupPlus α ψ := by
    intro h
    exact hjump (le_antisymm (P.apartment.affineRootGroupPlus_le α ψ) h)
  obtain ⟨u, hu, huplus⟩ := Set.not_subset.mp hnot
  obtain ⟨hu0, hu1, _⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  obtain ⟨p, hp⟩ := (hF α α.property u hu0 hu1).1.exists
  exact ⟨P.reflectionElement hp, u, hu, huplus, p, hp, rfl⟩

/-- A chosen actual normalizer representative at the given filtration jump. -/
def affineRankOneReflectionAtJump
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    normalizerPoints P.i :=
  Classical.choose (P.exists_pair_at_affineRootGroup_jump hF hψ hjump)

theorem affineRankOneReflectionAtJump_spec
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    ∃ u ∈ P.affineRootGroup α ψ, u ∉ P.apartment.affineRootGroupPlus α ψ ∧
      ∃ p, ∃ hp : RelativeRoot.IsOppositeFactorPair P.i
        (α : characterLattice P.S) u p,
        P.affineRankOneReflectionAtJump hF hψ hjump = P.reflectionElement hp :=
  Classical.choose_spec (P.exists_pair_at_affineRootGroup_jump hF hψ hjump)

/-- Both opposite factors of a supplied jump representative lie in the generated group. -/
theorem reflectionElement_mem_affineRankOneSubgroup
    (hψ : ψ.linear = rootForm P.i α)
    (hu : u ∈ P.affineRootGroup α ψ)
    (huplus : u ∉ P.apartment.affineRootGroupPlus α ψ)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    (P.reflectionElement hp : rationalPoints G) ∈ P.affineRankOneSubgroup α ψ := by
  obtain ⟨hu0, hu1, hlevel⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  obtain ⟨hleft, hright⟩ :=
    P.toValuationBuildingData.oppositeFactors_mem_neg_affineRootGroup hu0 hu1 hp hlevel
  exact mul_mem
    (mul_mem (P.affineRootGroup_neg_le_affineRankOneSubgroup α ψ hleft)
      (P.affineRootGroup_le_affineRankOneSubgroup α ψ hu))
    (P.affineRootGroup_neg_le_affineRankOneSubgroup α ψ hright)

/-- The chosen representative belongs to the original generated subgroup. -/
theorem affineRankOneReflectionAtJump_mem
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    (P.affineRankOneReflectionAtJump hF hψ hjump : rationalPoints G) ∈
      P.affineRankOneSubgroup α ψ := by
  obtain ⟨u, hu, huplus, p, hp, hm⟩ :=
    P.affineRankOneReflectionAtJump_spec hF hψ hjump
  rw [hm]
  exact P.reflectionElement_mem_affineRankOneSubgroup hψ hu huplus hp

/-- The chosen representative has the required actual action for every coroot of `ψ`. -/
theorem affineRankOneReflectionAtJump_action
    (hA : P.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ)
    {v : TranslationSpace P.i} (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v) :
    P.apartment.normalizerAffineEquiv (P.affineRankOneReflectionAtJump hF hψ hjump) =
      AffineRootSystem.affineReflection ψ hv.1 := by
  obtain ⟨u, hu, huplus, p, hp, hm⟩ :=
    P.affineRankOneReflectionAtJump_spec hF hψ hjump
  obtain ⟨hu0, hu1, hlevel⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  rw [hm]
  have hv' : AffineRootSystem.IsCoroot P.affineRoots (P.reflectionFunctional α u) v := by
    rwa [hlevel]
  simpa only [hlevel] using
    P.toValuationBuildingData.normalizerAffineEquiv_reflectionElement_eq_of_isCoroot
      hA hu0 hu1 hp hv'

/-- Conjugating the positive jump cell gives the negative jump cell for the same `m`.
The centralizer-zero conjugation premise is kept explicit. -/
theorem neg_affineRootGroup_subset_plus_union_reflectionCell
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hu : u ∈ P.affineRootGroup α ψ)
    (huplus : u ∉ P.apartment.affineRootGroupPlus α ψ)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p)
    (hmZ : ∀ z ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j),
      (P.reflectionElement hp : rationalPoints G)⁻¹ * z *
        (P.reflectionElement hp : rationalPoints G) ∈
          P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (P.affineRootGroup (-α.val) (-ψ) : Set (rationalPoints G)) ⊆
      (P.apartment.affineRootGroupPlus (-α.val) (-ψ) : Set (rationalPoints G)) ∪
        P.affineRankOneReflectionCell α ψ (P.reflectionElement hp) := by
  classical
  obtain ⟨hu0, hu1, hlevel⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  let m := P.reflectionElement hp
  have hUV : (P.affineRootGroup α ψ).map (MulAut.conj m.val).toMonoidHom =
      P.affineRootGroup (-α.val) (-ψ) := by
    simpa only [hlevel] using
      P.toValuationBuildingData.conj_affineRootGroup_reflectionElement hu0 hu1 hp
  have hVU : (P.affineRootGroup (-α.val) (-ψ)).map
      (MulAut.conj m.val).toMonoidHom = P.affineRootGroup α ψ := by
    simpa only [hlevel] using
      P.toValuationBuildingData.conj_neg_affineRootGroup_reflectionElement hu0 hu1 hp
  have hVUplus : (P.apartment.affineRootGroupPlus (-α.val) (-ψ)).map
      (MulAut.conj m.val).toMonoidHom = P.apartment.affineRootGroupPlus α ψ := by
    simpa only [hlevel] using
      P.toValuationBuildingData.conj_neg_affineRootGroupPlus_reflectionElement hu0 hu1 hp
  intro x hx
  by_cases hxplus : x ∈ P.apartment.affineRootGroupPlus (-α.val) (-ψ)
  · exact Or.inl hxplus
  right
  have hw : m.val * x * m.val⁻¹ ∈ P.affineRootGroup α ψ := by
    rw [← hVU]
    exact ⟨x, hx, rfl⟩
  have hwnot : m.val * x * m.val⁻¹ ∉ P.apartment.affineRootGroupPlus α ψ := by
    intro hwplus
    have h := inv_conj_mem_of_map_conj_eq hVUplus hwplus
    apply hxplus
    convert h using 1
    group
  obtain ⟨l, hl, z, hz, r, hr, heq⟩ :=
    P.affineRootGroup_diff_plus_subset_rootReflectionCell hA hZ hF hψ hu huplus hp
      ⟨hw, hwnot⟩
  change x ∈ Langlands.Group.FilteredRankOne.reflectionCell
    (P.affineRootGroup α ψ)
    (P.centralizerZero.map (rationalPoints.map P.centralizer.j)) m.val
  apply Langlands.Group.FilteredRankOne.mem_reflectionCell_iff.mpr
  refine ⟨m.val⁻¹ * l * m.val, inv_conj_mem_of_map_conj_eq hUV hl,
    m.val⁻¹ * rationalPoints.map P.centralizer.j z * m.val,
    hmZ _ ⟨z, hz, rfl⟩,
    m.val⁻¹ * r * m.val, inv_conj_mem_of_map_conj_eq hUV hr, ?_⟩
  calc
    _ = m.val⁻¹ * (l * m.val * rationalPoints.map P.centralizer.j z * r) * m.val := by
      group
    _ = m.val⁻¹ * (m.val * x * m.val⁻¹) * m.val := by rw [heq]
    _ = x := by group

/-- The actual two-cell equality from a supplied jump pair, an actual base-cell
subgroup, and centralizer-zero normalization. No such host input is inferred here. -/
theorem coe_affineRankOneSubgroup_eq_twoCell_of_pair
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hu : u ∈ P.affineRootGroup α ψ)
    (huplus : u ∉ P.apartment.affineRootGroupPlus α ψ)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p)
    (B : Subgroup (rationalPoints G))
    (hB : (B : Set (rationalPoints G)) = P.affineRankOneBaseCell α ψ)
    (hmZ : ∀ z ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j),
      (P.reflectionElement hp : rationalPoints G)⁻¹ * z *
        (P.reflectionElement hp : rationalPoints G) ∈
          P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
      P.affineRankOneBaseCell α ψ ∪
        P.affineRankOneReflectionCell α ψ (P.reflectionElement hp) := by
  obtain ⟨hu0, hu1, hlevel⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  have hsq : (P.reflectionElement hp : rationalPoints G) ^ 2 ∈
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
    obtain ⟨z, hz, heq⟩ :=
      P.exists_centralizerZero_map_eq_reflectionElement_sq hA hZ hu0 hu1 hp
    exact ⟨z, hz, heq⟩
  have hUV : (P.affineRootGroup α ψ).map
      (MulAut.conj (P.reflectionElement hp : rationalPoints G)).toMonoidHom =
        P.affineRootGroup (-α.val) (-ψ) := by
    simpa only [hlevel] using
      P.toValuationBuildingData.conj_affineRootGroup_reflectionElement hu0 hu1 hp
  have hVU : (P.affineRootGroup (-α.val) (-ψ)).map
      (MulAut.conj (P.reflectionElement hp : rationalPoints G)).toMonoidHom =
        P.affineRootGroup α ψ := by
    simpa only [hlevel] using
      P.toValuationBuildingData.conj_neg_affineRootGroup_reflectionElement hu0 hu1 hp
  have h := Langlands.Group.FilteredRankOne.coe_sup_eq_twoCell
    (P.apartment.affineRootGroupPlus_le (-α.val) (-ψ)) hB
    (P.reflectionElement_mem_affineRankOneSubgroup hψ hu huplus hp) hsq
    (fun z hz a ha =>
      (Subgroup.mem_normalizer_iff.mp
        (P.map_centralizerZero_le_normalizer_affineRootGroup α ψ hz) a).mp ha)
    hmZ (fun a ha => inv_conj_mem_of_map_conj_eq hVU ha)
    (fun b hb => inv_conj_mem_of_map_conj_eq hUV hb)
    (P.neg_affineRootGroup_subset_plus_union_reflectionCell hA hZ hF hψ hu huplus hp hmZ)
  change (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
    (B : Set (rationalPoints G)) ∪
      P.affineRankOneReflectionCell α ψ (P.reflectionElement hp) at h
  rwa [hB] at h

/-- The chosen actual jump representative gives the two-cell equality when the remaining
base-cell and centralizer-zero inputs are supplied. -/
theorem coe_affineRankOneSubgroup_eq_twoCell_at_jump
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ)
    (B : Subgroup (rationalPoints G))
    (hB : (B : Set (rationalPoints G)) = P.affineRankOneBaseCell α ψ)
    (hmZ : ∀ z ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j),
      (P.affineRankOneReflectionAtJump hF hψ hjump : rationalPoints G)⁻¹ * z *
        (P.affineRankOneReflectionAtJump hF hψ hjump : rationalPoints G) ∈
          P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
      P.affineRankOneBaseCell α ψ ∪ P.affineRankOneReflectionCell α ψ
        (P.affineRankOneReflectionAtJump hF hψ hjump) := by
  obtain ⟨u, hu, huplus, p, hp, hm⟩ :=
    P.affineRankOneReflectionAtJump_spec hF hψ hjump
  rw [hm] at hmZ ⊢
  exact P.coe_affineRankOneSubgroup_eq_twoCell_of_pair hA hZ hF hψ hu huplus hp B hB hmZ

end ParahoricBuildingData

end Langlands.Geometry.Building
