import Langlands.Automorphic.GroupSchemeFullAEL2
import Langlands.Automorphic.GroupSchemeParabolicL2ClosednessProof
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # The Hilbert structure on the original full AE cuspidal carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ρ" => quotientL2RightAction F G T i μQ hR
local notation "ρc" => fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc

/-- Package the unchanged full cusp submodule with its actual all-parabolic closedness. -/
def fullAEL2CuspidalClosedSubmodule : ClosedSubmodule ℂ (Lp ℂ 2 μQ) where
  toSubmodule := S
  isClosed' := (groupSchemeParabolicL2Closedness F G hPD hG T i hi I e hc).2.2

/-- The full cusp space uses exactly the existing submodule and inherited L2 geometry. -/
abbrev FullAEL2CuspidalHilbertSpace := S

/-- Completeness comes from actual closedness in the complete ambient L2 space. -/
instance fullAEL2Cuspidal_completeSpace : CompleteSpace S :=
  (fullAEL2CuspidalClosedSubmodule F G hPD hG T i hi I e hc).isClosed.completeSpace_coe

/-- The faithful cusp inclusion is an isometry for the unchanged inherited norm. -/
def fullAEL2CuspidalInclusionLI : S →ₗᵢ[ℂ] Lp ℂ 2 μQ :=
  (S).subtypeₗᵢ

/-- The Hilbert inclusion has exactly the linear map of the existing intertwiner. -/
theorem fullAEL2CuspidalInclusionLI_toLinearMap :
    (fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc).toLinearMap =
      (fullAEL2CuspidalToLp F G hPD hG T i hi I e hc).toLinearMap := rfl

/-- Orthogonal projection of the whole actual quotient L2 space into its full cusp carrier. -/
def fullAEL2CuspidalOrthogonalProjection : Lp ℂ 2 μQ →L[ℂ] S :=
  (S).orthogonalProjectionOnto

/-- The same orthogonal cusp projection, with ambient L2 codomain. -/
def fullAEL2CuspidalAmbientProjection : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ :=
  (S).starProjection

theorem norm_fullAEL2CuspidalOrthogonalProjection_le :
    ‖fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc‖ ≤ 1 :=
  (S).orthogonalProjectionOnto_norm_le

@[simp]
theorem fullAEL2CuspidalOrthogonalProjection_inclusion (φ : S) :
    fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ.val = φ :=
  (S).orthogonalProjectionOnto_mem_subspace_eq_self φ

theorem fullAEL2CuspidalAmbientProjection_mem (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ ∈ S :=
  (S).starProjection_apply_mem φ

/-- The ambient projection has precisely the original full AE cusp locus as its fixed set. -/
theorem fullAEL2CuspidalAmbientProjection_eq_self_iff (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ = φ ↔
      φ ∈ fullAEL2CuspidalLocus F G hPD hG T i :=
  (S).starProjection_eq_self_iff

/-- Every original right translation is a surjective isometry of the full cusp space. -/
def fullAEL2CuspidalRightTranslate (a : AdelicGroupPoints F G) : S ≃ₗᵢ[ℂ] S where
  toLinearEquiv :=
    { toLinearMap := ρc a
      invFun := ρc a⁻¹
      left_inv := (ρc).inv_self_apply a
      right_inv := (ρc).self_inv_apply a }
  norm_map' := norm_fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc a

@[simp]
theorem fullAEL2CuspidalRightTranslate_apply (a : AdelicGroupPoints F G) (φ : S) :
    fullAEL2CuspidalRightTranslate F G hPD hG T i hi I e hc a φ = ρc a φ := rfl

@[simp]
theorem fullAEL2CuspidalRightTranslate_symm_apply (a : AdelicGroupPoints F G) (φ : S) :
    (fullAEL2CuspidalRightTranslate F G hPD hG T i hi I e hc a).symm φ = ρc a⁻¹ φ := rfl

/-- Both directions of subgroup stability give equality with the original cusp submodule. -/
theorem map_fullAEL2CuspidalSubmodule_rightTranslate (a : AdelicGroupPoints F G) :
    (S).map (quotientL2RightTranslate F G T i μQ hR a).toLinearMap = S := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact (fullAEL2CuspidalSubrepresentation F G hPD hG T i hi I e hc).apply_mem_toSubmodule a hψ
  · intro hφ
    exact ⟨ρ a⁻¹ φ,
      (fullAEL2CuspidalSubrepresentation F G hPD hG T i hi I e hc).apply_mem_toSubmodule a⁻¹ hφ,
      (ρ).self_inv_apply a φ⟩

/-- The ambient orthogonal projection commutes with the unchanged right representation. -/
theorem fullAEL2CuspidalAmbientProjection_rightAction (a : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc (ρ a φ) =
      ρ a (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ) := by
  let f := quotientL2RightTranslate F G T i μQ hR a
  have hm : (S).map f.toLinearMap = S :=
    map_fullAEL2CuspidalSubmodule_rightTranslate F G hPD hG T i hi I e hc a
  let : ((S).map f.toLinearMap).HasOrthogonalProjection := by rw [hm]; infer_instance
  have h := f.map_starProjection (S) φ
  change (S).starProjection (f φ) = f ((S).starProjection φ)
  simpa only [hm] using h.symm

/-- The subtype-valued orthogonal projection intertwines the actual right actions. -/
theorem fullAEL2CuspidalOrthogonalProjection_rightAction (a : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc (ρ a φ) =
      ρc a (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ) := by
  apply Subtype.ext
  exact fullAEL2CuspidalAmbientProjection_rightAction F G hPD hG T i hi I e hc a φ

/-- The continuous orthogonal projection, also bundled as the original representation intertwiner. -/
def fullAEL2CuspidalProjectionIntertwiner : (ρ).IntertwiningMap (ρc) where
  toLinearMap := (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc).toLinearMap
  isIntertwining' a := by
    apply LinearMap.ext
    exact fullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG T i hi I e hc a

/-- Projection retracts the original faithful cusp intertwiner. -/
theorem fullAEL2CuspidalProjectionIntertwiner_comp_inclusion :
    (fullAEL2CuspidalProjectionIntertwiner F G hPD hG T i hi I e hc).comp
      (fullAEL2CuspidalToLp F G hPD hG T i hi I e hc) =
      Representation.IntertwiningMap.id (ρc) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro φ
  exact fullAEL2CuspidalOrthogonalProjection_inclusion F G hPD hG T i hi I e hc φ

end Langlands.Automorphic.GroupSchemeFunctions
