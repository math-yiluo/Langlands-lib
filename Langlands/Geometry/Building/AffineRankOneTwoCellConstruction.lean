import Langlands.Geometry.Building.AffineRankOneTwoCellAssembly
import Langlands.Geometry.Building.CentralizerZeroSCNormalizerConjugation

/-! # Actual rank-one two-cell witnesses -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- A witness carrying the exact three conclusions of the actual two-cell statement. -/
structure AffineRankOneTwoCellData
    (α : relativeRoots P.i) (ψ : P.Apartment →ᵃ[ℝ] ℝ) where
  representative : normalizerPoints P.i
  mem_subgroup : (representative : rationalPoints G) ∈ P.affineRankOneSubgroup α ψ
  action : ∀ (v : TranslationSpace P.i)
    (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v),
    P.apartment.normalizerAffineEquiv representative = AffineRootSystem.affineReflection ψ hv.1
  cells : (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
    P.affineRankOneBaseCell α ψ ∪
      P.affineRankOneReflectionCell α ψ (representative : rationalPoints G)

variable {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}

/-- The chosen jump representative normalizes the actual mapped centralizer-zero subgroup. -/
theorem affineRankOneReflectionAtJump_mem_normalizer_map_centralizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    (P.affineRankOneReflectionAtJump hF hψ hjump : rationalPoints G) ∈
      Subgroup.normalizer
        (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
          Set (rationalPoints G)) := by
  obtain ⟨u, hu, huplus, p, hp, hm⟩ :=
    P.affineRankOneReflectionAtJump_spec hF hψ hjump
  obtain ⟨hu0, hu1, _⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  rw [hm]
  exact P.reflectionElement_mem_normalizer_map_centralizerZero hA hZ hu0 hu1 hp

/-- Full actual two-cell witness once the literal base cell is a subgroup. -/
def affineRankOneTwoCellDataOfBaseSubgroup
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ)
    (B : Subgroup (rationalPoints G))
    (hB : (B : Set (rationalPoints G)) = P.affineRankOneBaseCell α ψ) :
    P.AffineRankOneTwoCellData α ψ where
  representative := P.affineRankOneReflectionAtJump hF hψ hjump
  mem_subgroup := P.affineRankOneReflectionAtJump_mem hF hψ hjump
  action _ hv := P.affineRankOneReflectionAtJump_action hA hF hψ hjump hv
  cells := P.coe_affineRankOneSubgroup_eq_twoCell_at_jump hA hZ hF hψ hjump B hB
    (fun z hz =>
      (Subgroup.mem_normalizer_iff''.mp
        (P.affineRankOneReflectionAtJump_mem_normalizer_map_centralizerZero
          hA hZ hF hψ hjump) z).mp hz)

end Langlands.Geometry.Building.ParahoricBuildingData
