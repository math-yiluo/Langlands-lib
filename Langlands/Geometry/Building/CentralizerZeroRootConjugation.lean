import Langlands.Geometry.Building.RootReflectionConjugation
import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Centralizer-zero conjugation of the actual affine root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData

variable (B : ValuationBuildingData G)

/-- A norm-one point of the actual centralizer preserves every affine functional. -/
theorem conjugateAffineFunctional_centralizerNormKernel
    {z : rationalPoints B.centralizer.Z}
    (hz : z ∈ rationalCommonNormKernel B.centralizer.Z)
    (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
    B.apartment.conjugateAffineFunctional (B.centralizer.toNormalizer z) ψ = ψ := by
  ext x
  simp only [KPApartmentData.conjugateAffineFunctional_apply, ← map_inv]
  rw [B.isOmegaCompatible.smul_eq_self
    ((rationalCommonNormKernel B.centralizer.Z).inv_mem hz) x]

/-- The norm-one centralizer preserves each actual weak affine root group. -/
theorem conj_affineRootGroup_centralizerNormKernel
    {z : rationalPoints B.centralizer.Z}
    (hz : z ∈ rationalCommonNormKernel B.centralizer.Z)
    (a : characterLattice B.S) (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
    (B.affineRootGroup a ψ).map
        (MulAut.conj (rationalPoints.map B.centralizer.j z)).toMonoidHom =
      B.affineRootGroup a ψ := by
  have hw : weylAction B.i (B.centralizer.toNormalizer z) a = a := by
    rw [show weylAction B.i (B.centralizer.toNormalizer z) = 1 from
      weylAction_centralizerToNormalizer B.centralizer.isRepresentedBy z]
    rfl
  change (B.affineRootGroup a ψ).map
    (MulAut.conj (B.centralizer.toNormalizer z : rationalPoints G)).toMonoidHom = _
  rw [B.apartment.conj_affineRootGroup, hw,
    B.conjugateAffineFunctional_centralizerNormKernel hz ψ]

/-- The norm-one centralizer preserves each actual strict affine root group. -/
theorem conj_affineRootGroupPlus_centralizerNormKernel
    {z : rationalPoints B.centralizer.Z}
    (hz : z ∈ rationalCommonNormKernel B.centralizer.Z)
    (a : characterLattice B.S) (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
    (B.apartment.affineRootGroupPlus a ψ).map
        (MulAut.conj (rationalPoints.map B.centralizer.j z)).toMonoidHom =
      B.apartment.affineRootGroupPlus a ψ := by
  have hw : weylAction B.i (B.centralizer.toNormalizer z) a = a := by
    rw [show weylAction B.i (B.centralizer.toNormalizer z) = 1 from
      weylAction_centralizerToNormalizer B.centralizer.isRepresentedBy z]
    rfl
  change (B.apartment.affineRootGroupPlus a ψ).map
    (MulAut.conj (B.centralizer.toNormalizer z : rationalPoints G)).toMonoidHom = _
  rw [B.apartment.conj_affineRootGroupPlus, hw,
    B.conjugateAffineFunctional_centralizerNormKernel hz ψ]

end ValuationBuildingData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

/-- The actual centralizer-zero image normalizes every weak affine root group. -/
theorem map_centralizerZero_le_normalizer_affineRootGroup
    (a : characterLattice P.S) (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      Subgroup.normalizer (P.affineRootGroup a ψ : Set (rationalPoints G)) := by
  rintro _ ⟨z, hz, rfl⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2
    (P.toValuationBuildingData.conj_affineRootGroup_centralizerNormKernel
      (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz) a ψ)

/-- The actual centralizer-zero image normalizes every strict affine root group. -/
theorem map_centralizerZero_le_normalizer_affineRootGroupPlus
    (a : characterLattice P.S) (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      Subgroup.normalizer (P.apartment.affineRootGroupPlus a ψ : Set (rationalPoints G)) := by
  rintro _ ⟨z, hz, rfl⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2
    (P.toValuationBuildingData.conj_affineRootGroupPlus_centralizerNormKernel
      (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz) a ψ)

/-- Actual conjugation by a centralizer-zero point, restricted to a weak root group. -/
def centralizerZeroAffineRootGroupAut
    (a : characterLattice P.S) (ψ : P.Apartment →ᵃ[ℝ] ℝ) (z : P.centralizerZero) :
    MulAut (P.affineRootGroup a ψ) :=
  ((MulAut.conj (rationalPoints.map P.centralizer.j z)).subgroupMap
    (P.affineRootGroup a ψ)).trans
      (MulEquiv.subgroupCongr
        (P.toValuationBuildingData.conj_affineRootGroup_centralizerNormKernel
          (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel z.property) a ψ))

/-- The restricted automorphism is literal conjugation in the original rational group. -/
@[simp]
theorem coe_centralizerZeroAffineRootGroupAut
    (a : characterLattice P.S) (ψ : P.Apartment →ᵃ[ℝ] ℝ)
    (z : P.centralizerZero) (g : P.affineRootGroup a ψ) :
    (P.centralizerZeroAffineRootGroupAut a ψ z g : rationalPoints G) =
      rationalPoints.map P.centralizer.j z * g *
        (rationalPoints.map P.centralizer.j z)⁻¹ :=
  rfl

end ParahoricBuildingData

end Langlands.Geometry.Building
