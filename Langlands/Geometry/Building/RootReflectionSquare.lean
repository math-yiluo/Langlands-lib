import Langlands.Geometry.Building.FilteredRootReflectionCells
import Langlands.Geometry.Building.IwahoriWeyl
import Langlands.GroupScheme.Rational.RootFactorPairSymmetry

/-! # Actual centralizer-zero lifts of reflection squares -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {α : relativeRoots B.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- Inversion preserves the valuation functional of a nonidentity root point. -/
theorem reflectionFunctional_inv (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1) :
    B.reflectionFunctional α u⁻¹ = B.reflectionFunctional α u := by
  apply AffineMap.ext
  intro x
  apply WithTop.coe_injective (α := ℝ)
  rw [B.coe_reflectionFunctional_apply ((B.rootGroup α).inv_mem hu)
    (inv_ne_one.mpr hu1), B.coe_reflectionFunctional_apply hu hu1,
    x.isValuation.apply_inv]

/-- Reversing and inverting the supplied pair gives the inverse normalizer point. -/
theorem reflectionElement_inv
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    B.reflectionElement (hp.inv B.i) = (B.reflectionElement hp)⁻¹ := by
  apply Subtype.ext
  simp only [coe_reflectionElement, Subgroup.coe_inv, mul_inv_rev, mul_assoc]

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    {α : relativeRoots P.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The square of a supplied reflection representative has an actual
centralizer-zero preimage under the explicit cover comparison. -/
theorem exists_centralizerZero_map_eq_reflectionElement_sq
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    ∃ z ∈ P.centralizerZero, rationalPoints.map P.centralizer.j z =
      ((P.reflectionElement hp) ^ 2 : normalizerPoints P.i).val := by
  obtain ⟨z, hz, hjz⟩ := P.reflectionElement_inv_mul_eq_centralizerZero
    hA hZ hu hu1 ((P.rootGroup α).inv_mem hu) (inv_ne_one.mpr hu1) hp
    (hp.inv P.i) (P.toValuationBuildingData.reflectionFunctional_inv hu hu1).symm
  refine ⟨z⁻¹, P.centralizerZero.inv_mem hz, ?_⟩
  rw [map_inv, hjz, P.toValuationBuildingData.reflectionElement_inv hp]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, pow_two]

/-- A chosen actual centralizer-zero lift of the square of a supplied representative. -/
def reflectionSquareCentralizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    P.centralizerZero :=
  ⟨Classical.choose (P.exists_centralizerZero_map_eq_reflectionElement_sq hA hZ hu hu1 hp),
    (Classical.choose_spec
      (P.exists_centralizerZero_map_eq_reflectionElement_sq hA hZ hu hu1 hp)).1⟩

/-- The chosen lift maps to the literal square in the original rational group. -/
theorem map_reflectionSquareCentralizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    rationalPoints.map P.centralizer.j (P.reflectionSquareCentralizerZero hA hZ hu hu1 hp) =
      ((P.reflectionElement hp) ^ 2 : normalizerPoints P.i).val :=
  (Classical.choose_spec
    (P.exists_centralizerZero_map_eq_reflectionElement_sq hA hZ hu hu1 hp)).2

/-- The square belongs to the actual normalizer-zero subgroup. -/
theorem reflectionElement_sq_mem_normalizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    (P.reflectionElement hp) ^ 2 ∈ P.normalizerZero := by
  obtain ⟨z, hz, hjz⟩ := P.exists_centralizerZero_map_eq_reflectionElement_sq hA hZ hu hu1 hp
  exact ⟨z, hz, Subtype.ext hjz⟩

end ParahoricBuildingData

end Langlands.Geometry.Building
