import Langlands.Geometry.Building.SplitTorusValuation
import Langlands.GroupScheme.Torus.SplitPointTopology
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Compact units and smooth characters of actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.SplitTorus

/-- A smooth complex character has norm one on every compact subgroup. -/
theorem norm_eq_one_on_compact_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G))
    {a : G} (ha : a ∈ K) : ‖(χ a : ℂ)‖ = 1 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : Subgroup K := χ.ker.subgroupOf K
  have hU : IsOpen (U : Set K) := Subgroup.subgroupOf_isOpen K χ.ker hχ
  let : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have hmem := U.pow_index_mem ⟨a, ha⟩
  have h1 : χ a ^ U.index = 1 := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.coe_pow, MonoidHom.mem_ker, map_pow] at h
    exact h
  have h2 : ‖(χ a : ℂ)‖ ^ U.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) U.index_ne_zero_of_finite).mp h2

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The actual valuation-ring units form a compact subgroup of field units. -/
theorem isCompact_fieldUnitGroup : IsCompact (FML.unitGroup F : Set Fˣ) := by
  let S : Set F := {x | ValuativeRel.valuation F x = 1}
  have hS : IsCompact S := by
    have hcl : IsClosed S := by
      simpa only [Valuation.restrict_eq_one_iff] using
        (ValuativeRel.valuation F).isClosed_sphere (r := 1)
    exact (IsNonarchimedeanLocalField.isCompact_closedBall F 1).of_isClosed_subset hcl
      fun x hx => le_of_eq hx
  have he : (FML.unitGroup F : Set Fˣ) = Units.val ⁻¹' S := by
    ext a
    exact Valuation.mem_unitGroup_iff F (ValuativeRel.valuation F) a
  rw [he]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS fun x hx => ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    have hx' : ValuativeRel.valuation F (0 : F) = 1 := hx
    rw [map_zero] at hx'
    exact zero_ne_one hx'
  exact ⟨Units.mk0 x hx0, rfl⟩

variable (I : Type u) [Fintype I]

local notation "𝕋" => splitTorus (Spec (CommRingCat.of F)) I

local instance splitAffineHom : IsAffineHom (𝕋).X.hom :=
  isAffineHom_splitTorus _ _

local instance splitAffine : IsAffine (𝕋).X.left :=
  isAffine_of_isAffineHom (𝕋).X.hom

/-- The canonical rational-point topology has the published finite unit coordinates. -/
def coordinatesHomeomorph :
    letI := rationalPointTopology F (𝕋).X
    rationalPoints 𝕋 ≃ₜ (I → Fˣ) := by
  letI := rationalPointTopology F (𝕋).X
  letI := (𝕋).affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of F) F)
  exact (rationalPointsAffineHomeomorph 𝕋).trans
    (splitTorus.affinePointsHomeomorph I (CommRingCat.of F)
      (CommAlgCat.of (CommRingCat.of F) F)).toHomeomorph

theorem coordinatesHomeomorph_apply (a : rationalPoints 𝕋) :
    coordinatesHomeomorph F I a =
      splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of F))) a := by
  funext i
  change Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of (CommRingCat.of F) F)
      (rationalPointEquiv F (𝕋).X a ≫
        (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of F))).toGrp) i).hom.hom) =
    rationalCharacterEval
      (Additive.ofMul (Limits.Pi.π
        (fun _ : I => (Gm (Spec (CommRingCat.of F))).toGrp) i)) a
  exact (rationalCharacterEval_eq_affineUnitsEquiv 𝕋
    (Additive.ofMul (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of F))).toGrp) i))
    a).symm

/-- Compactness of the actual coordinate split torus's common norm kernel. -/
theorem isCompact_splitCommonNormKernel :
    letI := rationalPointTopology F (𝕋).X
    IsCompact (rationalCommonNormKernel 𝕋 : Set (rationalPoints 𝕋)) := by
  let := rationalPointTopology F (𝕋).X
  have hK : IsCompact (Set.pi Set.univ fun _ : I => (FML.unitGroup F : Set Fˣ)) :=
    by simpa only [Set.pi, Set.mem_univ, forall_true_left] using
      isCompact_pi_infinite (fun _ : I => isCompact_fieldUnitGroup F)
  have he : (rationalCommonNormKernel 𝕋 : Set (rationalPoints 𝕋)) =
      coordinatesHomeomorph F I ⁻¹'
        Set.pi Set.univ (fun _ : I => (FML.unitGroup F : Set Fˣ)) := by
    ext a
    rw [← SplitTorusValuation.integralUnitKernel_eq_rationalCommonNormKernel F I]
    change a ∈ SplitTorusValuation.integralUnitKernel F I ↔ _
    rw [SplitTorusValuation.mem_integralUnitKernel]
    simp only [Set.mem_preimage, coordinatesHomeomorph_apply, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    rfl
  rw [he]
  exact (coordinatesHomeomorph F I).isCompact_preimage.mpr hK

end Langlands.Plancherel.SplitTorus
