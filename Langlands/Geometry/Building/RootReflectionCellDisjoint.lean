import Langlands.Geometry.Building.FilteredRootReflectionCells
import Langlands.GroupScheme.Rational.RootSubgroupSeparation

/-! # Separation of actual reflection cells from strict affine root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- The actual cell `U_{-ψ} m Z(F) U_{-ψ}`, with unrestricted centralizer point. -/
def rootReflectionCentralizerCell (a : characterLattice B.S) (ψ : B.Apartment →ᵃ[ℝ] ℝ)
    (m : normalizerPoints B.i) : Set (rationalPoints G) :=
  {v | ∃ l ∈ B.affineRootGroup (-a) (-ψ),
    ∃ z : rationalPoints B.centralizer.Z, ∃ r ∈ B.affineRootGroup (-a) (-ψ),
      l * m.val * rationalPoints.map B.centralizer.j z * r = v}

variable {α : relativeRoots B.i} {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    {m : normalizerPoints B.i}

/-- A cell with a root-flipping normalizer is disjoint from the strict affine root group.
The centralizer point may be arbitrary. -/
theorem disjoint_affineRootGroupPlus_rootReflectionCentralizerCell
    (hψ : ψ.linear = rootForm B.i α)
    (hm : weylAction B.i m (α : characterLattice B.S) = -α.val) :
    Disjoint (B.apartment.affineRootGroupPlus α ψ : Set (rationalPoints G))
      (B.rootReflectionCentralizerCell α ψ m) := by
  refine Set.disjoint_left.mpr ?_
  intro w hw hcell
  obtain ⟨l, hl, z, r, hr, heq⟩ := hcell
  let n : normalizerPoints B.i := m * B.centralizer.toNormalizer z
  have hn : n.val = m.val * rationalPoints.map B.centralizer.j z := rfl
  have hnflip : weylAction B.i n (-α.val) = -(-α.val) := by
    have hz : weylAction B.i (B.centralizer.toNormalizer z) = 1 :=
      weylAction_centralizerToNormalizer B.centralizer.isRepresentedBy z
    simp only [n, map_mul, hz, mul_one, map_neg, hm]
  have hl0 := B.apartment.affineRootGroup_le_rootGroupPoints (-α.val) (-ψ) hl
  have hr0 := B.apartment.affineRootGroup_le_rootGroupPoints (-α.val) (-ψ) hr
  have hlInv := (rootGroupPoints B.i (-α.val)).inv_mem hl0
  have hrInv := (rootGroupPoints B.i (-α.val)).inv_mem hr0
  have hprod : n.val = l⁻¹ * w * r⁻¹ := by
    rw [← heq, hn]
    group
  have hpN : l⁻¹ * w * r⁻¹ ∈ normalizerPoints B.i := by
    rw [← hprod]
    exact n.property
  by_cases hw1 : w = 1
  · have hn0 : n.val ∈ rootGroupPoints B.i (-α.val) := by
      rw [hprod, hw1, mul_one]
      exact (rootGroupPoints B.i (-α.val)).mul_mem hlInv hrInv
    exact RelativeRoot.normalizer_not_mem_subgroup_of_flip B.i
      B.isMaximalSplitTorus.isSplitSubtorus.1 (neg_ne_zero.mpr α.property.1) n hnflip hn0
  · let x : B.Apartment := Classical.arbitrary B.Apartment
    obtain ⟨hw0, hwt⟩ := (KPApartmentData.mem_affineRootGroupPlus_iff hψ x).mp hw
    obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x α.property hw0 hw1
    have h5 := x.isValuation.opposite α α.property w hw0 hw1 l⁻¹ hlInv r⁻¹ hrInv hpN
    rw [ht] at h5 hwt
    have hleft : ((-ψ x : ℝ) : WithTop ℝ) ≤ x.val (-α.val) l⁻¹ := by
      exact (Subgroup.mem_iInf.mp
        ((B.affineRootGroup (-α.val) (-ψ)).inv_mem hl) x).2
    rw [withTop_eq_neg_of_add_eq_zero h5, WithTop.coe_le_coe] at hleft
    rw [WithTop.coe_lt_coe] at hwt
    linarith

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Restricting the centralizer factor gives the actual centralizer-zero cell. -/
theorem rootReflectionCell_subset_rootReflectionCentralizerCell
    (a : characterLattice P.S) (ψ : P.Apartment →ᵃ[ℝ] ℝ) (m : normalizerPoints P.i) :
    P.rootReflectionCell a ψ m ⊆
      P.toValuationBuildingData.rootReflectionCentralizerCell a ψ m := by
  rintro w ⟨l, hl, z, _, r, hr, heq⟩
  exact ⟨l, hl, z, r, hr, heq⟩

variable {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    {m : normalizerPoints P.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The actual centralizer-zero cell is disjoint from the strict affine root group. -/
theorem disjoint_affineRootGroupPlus_rootReflectionCell
    (hψ : ψ.linear = rootForm P.i α)
    (hm : weylAction P.i m (α : characterLattice P.S) = -α.val) :
    Disjoint (P.apartment.affineRootGroupPlus α ψ : Set (rationalPoints G))
      (P.rootReflectionCell α ψ m) :=
  (P.toValuationBuildingData.disjoint_affineRootGroupPlus_rootReflectionCentralizerCell
    hψ hm).mono_right (P.rootReflectionCell_subset_rootReflectionCentralizerCell α ψ m)

/-- Strict-cell disjointness for any supplied opposite pair of a nonidentity root point. -/
theorem disjoint_affineRootGroupPlus_reflectionElementCell
    (hψ : ψ.linear = rootForm P.i α)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    Disjoint (P.apartment.affineRootGroupPlus α ψ : Set (rationalPoints G))
      (P.rootReflectionCell α ψ (P.reflectionElement hp)) :=
  P.disjoint_affineRootGroupPlus_rootReflectionCell hψ
    (hp.weylAction_eq_neg P.i P.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1)

end ParahoricBuildingData

end Langlands.Geometry.Building
