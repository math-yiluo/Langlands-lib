import Langlands.Geometry.Building.AffineRankOneTwoCellConstruction
import Langlands.Geometry.Building.AffineRankOneBaseSubgroup

/-! # Actual rank-one two-cell data from the two remaining structural inputs -/

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
    {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}

/-- Construct the exact two-cell data using the actual base-cell subgroup. -/
def affineRankOneTwoCellData
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    P.AffineRankOneTwoCellData α ψ :=
  P.affineRankOneTwoCellDataOfBaseSubgroup hA hZ hF hψ hjump
    (P.affineRankOneBaseSubgroup α ψ) (P.coe_affineRankOneBaseSubgroup hA hZ hF hψ)

/-- The literal cell equality for the original chosen jump representative. -/
theorem coe_affineRankOneSubgroup_eq_twoCell_of_coverImage_factorization
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
      P.affineRankOneBaseCell α ψ ∪
        P.affineRankOneReflectionCell α ψ
          (P.affineRankOneReflectionAtJump hF hψ hjump : rationalPoints G) :=
  (P.affineRankOneTwoCellData hA hZ hF hψ hjump).cells

/-- Every conclusion of the published target under the explicit cover-image
comparison and actual factor-pair existence. -/
theorem exists_affineRankOneTwoCell_of_coverImage_factorization
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hjump : P.apartment.affineRootGroupPlus α ψ ≠ P.affineRootGroup α ψ) :
    ∃ m : normalizerPoints P.i,
      (m : rationalPoints G) ∈ P.affineRankOneSubgroup α ψ ∧
      (∀ (v : TranslationSpace P.i) (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v),
        P.apartment.normalizerAffineEquiv m = AffineRootSystem.affineReflection ψ hv.1) ∧
      (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
        P.affineRankOneBaseCell α ψ ∪
          P.affineRankOneReflectionCell α ψ (m : rationalPoints G) := by
  let d := P.affineRankOneTwoCellData hA hZ hF hψ hjump
  exact ⟨d.representative, d.mem_subgroup, d.action, d.cells⟩

end Langlands.Geometry.Building.ParahoricBuildingData
