import Langlands.Geometry.FormalGroup.HarrisSplitGroupScheme
import Langlands.Geometry.FormalGroup.HarrisIntegralComponentKernel
import Langlands.GroupScheme.FiniteAlgebraRationalTopology
import Langlands.GroupScheme.MultiplicativeRationalTopology
import Langlands.AlgebraicGeometry.PointTopology.RationalSchemePoints

/-! # Integral units in Harris's rational-character kernel -/

noncomputable section
universe u

namespace Langlands.FormalGroup.Harris

open _root_.AlgebraicGeometry CategoryTheory MulOpposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Shimura.LocalDivision Langlands.CentralDivision
open scoped CategoryTheory.MonObj Topology

variable {k B : Type u} [Field k] {n : ℕ}
private abbrev scalarGroup := (Gm (Spec (CommRingCat.of k))).toGrp

section Ring

variable [Ring B] [Algebra k B] (b : Module.Basis (Fin n) k Bᵐᵒᵖ)

/-- Parametrize the actual rational points by their opposite unit and scalar multiplier. -/
def rationalPointsOfSplitUnits : (Bᵐᵒᵖ)ˣ × kˣ ≃* rationalPoints (splitGroupScheme b) :=
  (splitSimilitudeCoordinates k B).symm.trans (splitGroupRationalPointsEquiv b).symm

private theorem rationalPointsOfSplitUnits_pair (z : (Bᵐᵒᵖ)ˣ × kˣ) :
    rationalPointsOfSplitUnits b z =
      lift ((FiniteAlgebraUnits.rationalPointsEquiv b).symm z.1)
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm z.2) := by
  change (splitGroupRationalPointsEquiv b).symm ((splitSimilitudeCoordinates k B).symm z) = _
  change (productPointsEquiv (FiniteAlgebraUnits.groupScheme b) (scalarGroup (k := k)) _).symm
    (((FiniteAlgebraUnits.rationalPointsEquiv b).prodCongr
      (Gm.affinePointsEquiv (𝟙 _))).symm
        ((splitSimilitudeCoordinates k B) ((splitSimilitudeCoordinates k B).symm z))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The parametrization is continuous for the canonical rational-point topology. -/
theorem continuous_rationalPointsOfSplitUnits [TopologicalSpace k] [IsTopologicalRing k]
    [ContinuousInv₀ k] [IsOpenUnits k] [TopologicalSpace Bᵐᵒᵖ]
    (hb : ∀ i, Continuous fun a : Bᵐᵒᵖ => b.repr a i) :
    Continuous[inferInstance, rationalPointTopology k (splitGroupScheme b).X]
      (rationalPointsOfSplitUnits b) := by
  let U := (FiniteAlgebraUnits.groupScheme b).X
  let V := (scalarGroup (k := k)).X
  have : IsAffine (U ⊗ V).left := splitGroupScheme_isAffine b
  have hpair := continuous_rationalSchemePointPair k U V
  rw [← rationalPointTopology_eq_rationalSchemeTopology,
    ← rationalPointTopology_eq_rationalSchemeTopology,
    ← rationalPointTopology_eq_rationalSchemeTopology] at hpair
  let : TopologicalSpace (RationalPoint k U) := rationalPointTopology k U
  let : TopologicalSpace (RationalPoint k V) := rationalPointTopology k V
  let : TopologicalSpace (rationalPoints (splitGroupScheme b)) :=
    rationalPointTopology k (splitGroupScheme b).X
  have hu := (FiniteAlgebraUnits.rationalPointOfUnit b hb).continuous_toFun
  have hv := (Gm.rationalPointOfUnit (k := k)).continuous_toFun
  have h := hpair.comp ((hu.comp continuous_fst).prodMk (hv.comp continuous_snd))
  convert h using 1
  funext z
  exact rationalPointsOfSplitUnits_pair b z

end Ring

section LocalField

variable {F : Type u} [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [DivisionRing B] [Algebra k B] [Algebra F B] [FiniteDimensional F B]
variable (b : Module.Basis (Fin n) k Bᵐᵒᵖ)

local instance : NontriviallyNormedField k := LocalGalois.localNormedField k
local instance : CompleteSpace k := LocalGalois.localNormedField_complete k
local instance : IsUltrametricDist k := LocalGalois.localNormedField_ultrametric k
local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
/-- Harris's `C_p` for the split group, defined by all actual rational characters
having integral-unit values. -/
def splitRationalCharacterKernel : Subgroup (splitInvolution k B).similitudes :=
  ⨅ χ : rationalCharacters (splitGroupScheme b),
    (integerRing k k).toSubmonoid.units.comap
      ((rationalCharacterEval χ).comp (splitGroupRationalPointsEquiv b).symm.toMonoidHom)

/-- The integral-unit condition on every actual character is the absolute-value
kernel condition in Harris's component quotient. -/
theorem mem_splitRationalCharacterKernel_iff (g : (splitInvolution k B).similitudes) :
    g ∈ splitRationalCharacterKernel b ↔
      ∀ χ : rationalCharacters (splitGroupScheme b),
        ‖(rationalCharacterEval χ ((splitGroupRationalPointsEquiv b).symm g) : k)‖ = 1 := by
  rw [splitRationalCharacterKernel, Subgroup.mem_iInf]
  apply forall_congr'
  intro χ
  let a := rationalCharacterEval χ ((splitGroupRationalPointsEquiv b).symm g)
  change a ∈ (integerRing k k).toSubmonoid.units ↔ ‖(a : k)‖ = 1
  have hnorm (x : k) : regularAbsoluteValue k k x = ‖x‖ := by
    simpa only [Algebra.algebraMap_self_apply] using (regularAbsoluteValue_algebraMap k k x)
  change (regularAbsoluteValue k k (a : k) ≤ 1 ∧
    regularAbsoluteValue k k (↑a⁻¹ : k) ≤ 1) ↔ _
  rw [hnorm, hnorm, Units.val_inv_eq_inv_val, norm_inv,
    inv_le_one₀ (norm_pos_iff.mpr a.ne_zero), le_antisymm_iff]

variable [TopologicalSpace B] [IsModuleTopology F B]

private def oppositeUnitOf (x : Bˣ) : (Bᵐᵒᵖ)ˣ := Units.opEquiv.symm (op x)

private theorem continuous_oppositeUnitOf : Continuous (oppositeUnitOf (B := B)) := by
  apply Units.continuous_iff.mpr
  exact ⟨continuous_op.comp Units.continuous_val, continuous_op.comp Units.continuous_coe_inv⟩

variable (F) in
/-- The opposite-unit and multiplier coordinates of the integral subgroup form a compact set. -/
theorem isCompact_splitIntegerUnitCoordinates :
    IsCompact (splitSimilitudeCoordinates k B '' (splitIntegerUnits k F B : Set _)) := by
  have hop : IsCompact (oppositeUnitOf ''
      ((maximalCompactLevel F B).subgroup : Set Bˣ)) :=
    (maximalCompactLevel F B).isCompact.image continuous_oppositeUnitOf
  have h := hop.prod (maximalCompactLevel k k).isCompact
  convert h using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (Units.opEquiv (splitSimilitudeCoordinates k B x).1).unop ∈
      (maximalCompactLevel F B).subgroup ∧
      (splitSimilitudeCoordinates k B x).2 ∈ (maximalCompactLevel k k).subgroup at hx
    refine ⟨⟨(Units.opEquiv (splitSimilitudeCoordinates k B x).1).unop, hx.1, ?_⟩, hx.2⟩
    simp only [oppositeUnitOf, op_unop, MulEquiv.symm_apply_apply]
  · rintro ⟨⟨x, hx, hxe⟩, he⟩
    refine ⟨(splitSimilitudeCoordinates k B).symm z, ?_, MulEquiv.apply_symm_apply _ _⟩
    change (Units.opEquiv (splitSimilitudeCoordinates k B
        ((splitSimilitudeCoordinates k B).symm z)).1).unop ∈
      (maximalCompactLevel F B).subgroup ∧
      (splitSimilitudeCoordinates k B ((splitSimilitudeCoordinates k B).symm z)).2 ∈
        (maximalCompactLevel k k).subgroup
    rw [MulEquiv.apply_symm_apply, ← hxe, oppositeUnitOf, MulEquiv.apply_symm_apply]
    exact ⟨hx, he⟩

variable (F) in
/-- The subgroup in the two integral unit coordinates lies in the actual common
rational-character kernel of the split group. -/
theorem splitIntegerUnits_le_splitRationalCharacterKernel [Algebra k F] [IsScalarTower k F B]
    (hkF : Continuous (algebraMap k F)) :
    splitIntegerUnits k F B ≤ splitRationalCharacterKernel b := by
  let : T2Space B := t2Space_of_isModuleTopology F B
  let : IsTopologicalAddGroup B := IsModuleTopology.isTopologicalAddGroup F B
  let : FiniteDimensional k B := Module.Finite.of_basis (b.map (opLinearEquiv k).symm)
  have hsmul : ContinuousSMul k B := ⟨by
    have h := (continuous_smul (M := F) (X := B)).comp
      ((hkF.comp continuous_fst).prodMk continuous_snd)
    convert h using 1
    funext p
    exact (algebraMap_smul F p.1 p.2).symm⟩
  have hb (i : Fin n) : Continuous fun a : Bᵐᵒᵖ => b.repr a i := by
    let l : B →ₗ[k] k := (b.coord i).comp (opLinearEquiv k).toLinearMap
    exact l.continuous_of_finiteDimensional.comp continuous_unop
  let : TopologicalSpace (rationalPoints (splitGroupScheme b)) :=
    rationalPointTopology k (splitGroupScheme b).X
  have hc := continuous_rationalPointsOfSplitUnits b hb
  intro g hg
  refine Subgroup.mem_iInf.mpr fun χ => ?_
  let map := (rationalCharacterEval χ).comp (rationalPointsOfSplitUnits b).toMonoidHom
  let H := (splitIntegerUnits k F B).map (splitSimilitudeCoordinates k B).toMonoidHom
  have hH : IsCompact (H : Set ((Bᵐᵒᵖ)ˣ × kˣ)) := isCompact_splitIntegerUnitCoordinates (B := B) F
  have hmap : Continuous map := (continuous_rationalCharacterEval _ χ).comp hc
  have hcompact : IsCompact (H.map map : Set kˣ) := hH.image hmap
  have hle := le_maximalCompactLevel_of_isCompact k k (H.map map) hcompact
  change (rationalCharacterEval χ) ((splitGroupRationalPointsEquiv b).symm g) ∈
    (maximalCompactLevel k k).subgroup
  apply hle
  refine ⟨splitSimilitudeCoordinates k B g, ⟨g, hg, rfl⟩, ?_⟩
  change (rationalCharacterEval χ) ((splitGroupRationalPointsEquiv b).symm
    ((splitSimilitudeCoordinates k B).symm (splitSimilitudeCoordinates k B g))) = _
  rw [MulEquiv.symm_apply_apply]

end LocalField
end Langlands.FormalGroup.Harris
