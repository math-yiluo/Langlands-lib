import Langlands.Shimura.PEL.HarrisIntegralTateImages

/-! # Source-stabilizing refinements of actual Harris adelic levels -/

noncomputable section

open scoped TensorProduct
open Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "L" => D.harrisHodgePELIntegralLattice C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C

local instance : Module Rf Vf := Module.compHom _ (Rf).subtype
local instance : TopologicalSpace Vf := moduleTopology Af Vf

private def sourceIntegralBasis :
    Module.Basis (Fin (Module.finrank ℤ L)) ℤ L :=
  Module.finBasis ℤ L

private def sourceRationalBasis :
    Module.Basis (Fin (Module.finrank ℤ L)) ℚ A :=
  (sourceIntegralBasis D C).extendOfIsLattice ℚ

private def basisSpan {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ A) :
    Submodule Rf Vf :=
  Submodule.span Rf (Set.range (fun i => (1 : Af) ⊗ₜ[ℚ] b i))

private theorem basisSpan_mem_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ A) (v : Vf) :
    v ∈ basisSpan b ↔ ∀ i, (b.baseChange Af).repr v i ∈ Rf := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      intro i
      change (b.baseChange Af).repr ((1 : Af) ⊗ₜ[ℚ] b j) i ∈ Rf
      rw [← Module.Basis.baseChange_apply]
      simp only [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact (Rf).one_mem
      · exact (Rf).zero_mem
    | zero =>
      intro i
      simpa only [map_zero, Finsupp.zero_apply] using (Rf).zero_mem
    | add x y hx hy hx' hy' =>
      intro i
      simpa using (Rf).add_mem (hx' i) (hy' i)
    | smul r x hx hx' =>
      intro i
      change (b.baseChange Af).repr ((r : Af) • x) i ∈ Rf
      simpa using (Rf).mul_mem r.property (hx' i)
  · intro hv
    rw [← (b.baseChange Af).sum_repr v]
    apply Submodule.sum_mem
    intro i _
    rw [Module.Basis.baseChange_apply]
    change (⟨(b.baseChange Af).repr v i, hv i⟩ : Rf) •
      ((1 : Af) ⊗ₜ[ℚ] b i) ∈ basisSpan b
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem basisSpan_isOpen {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ A) : IsOpen (basisSpan b : Set Vf) := by
  have heq : (basisSpan b : Set Vf) =
      ⋂ i, {v : Vf | (b.baseChange Af).repr v i ∈ Rf} := by
    ext v
    constructor
    · intro hv
      exact Set.mem_iInter.mpr ((basisSpan_mem_iff b v).mp hv)
    · intro hv
      exact (basisSpan_mem_iff b v).mpr (Set.mem_iInter.mp hv)
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply Global.isOpen_integralFiniteAdeles ℚ |>.preimage
  exact (IsModuleTopology.continuous_of_linearMap ((b.baseChange Af).coord i)).congr
    (fun v => (b.baseChange Af).coord_apply i v)

private theorem sourceSpan_eq_basisSpan :
    Λf = basisSpan (sourceRationalBasis D C) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [← (sourceIntegralBasis D C).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul]
    apply Submodule.sum_mem
    intro i _
    apply (basisSpan (sourceRationalBasis D C)).toAddSubgroup.zsmul_mem
    exact Submodule.subset_span ⟨i, by
      simp only [sourceRationalBasis, Module.Basis.extendOfIsLattice_apply]⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (1 : Af) ⊗ₜ[ℚ] (sourceRationalBasis D C i) ∈ Λf
    rw [sourceRationalBasis, Module.Basis.extendOfIsLattice_apply]
    exact D.harrisHodgePELIntegralAdeleSpan_tmul C (sourceIntegralBasis D C i)

/-- The actual integral source span is open in the canonical adelic module topology. -/
theorem harrisHodgePELIntegralAdeleSpan_isOpen : IsOpen (Λf : Set Vf) := by
  rw [sourceSpan_eq_basisSpan D C]
  exact basisSpan_isOpen _

private theorem basisSpan_map_mem {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ A) (f : Vf →ₗ[Af] Vf)
    (hf : ∀ i, f ((1 : Af) ⊗ₜ[ℚ] b i) ∈ basisSpan b)
    {v : Vf} (hv : v ∈ basisSpan b) : f v ∈ basisSpan b := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact hf i
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x y hx hy hx' hy' =>
    simpa only [map_add] using (basisSpan b).add_mem hx' hy'
  | smul r x hx hx' =>
    change f ((r : Af) • x) ∈ basisSpan b
    rw [map_smul]
    exact (basisSpan b).smul_mem r hx'

private theorem sourceBasis_mem (i : Fin (Module.finrank ℤ L)) :
    (1 : Af) ⊗ₜ[ℚ] sourceRationalBasis D C i ∈ Λf := by
  rw [sourceRationalBasis, Module.Basis.extendOfIsLattice_apply]
  exact D.harrisHodgePELIntegralAdeleSpan_tmul C (sourceIntegralBasis D C i)

private theorem sourceSpan_map_mem (f : Vf →ₗ[Af] Vf)
    (hf : ∀ i, f ((1 : Af) ⊗ₜ[ℚ] sourceRationalBasis D C i) ∈ Λf)
    {v : Vf} (hv : v ∈ Λf) : f v ∈ Λf := by
  rw [sourceSpan_eq_basisSpan D C] at hv ⊢
  exact basisSpan_map_mem _ f (fun i => by
    rw [← sourceSpan_eq_basisSpan D C]
    exact hf i) hv

local notation "G" => ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)

private theorem stabilizer_mem_iff (g : G) :
    g ∈ harrisIntegralAdeleStabilizer D C ↔
      (∀ i, g.val.1 ((1 : Af) ⊗ₜ[ℚ] sourceRationalBasis D C i) ∈ Λf) ∧
      (∀ i, g.val.1.symm ((1 : Af) ⊗ₜ[ℚ] sourceRationalBasis D C i) ∈ Λf) := by
  constructor
  · intro hg
    constructor
    · intro i
      exact (hg _).mpr (sourceBasis_mem D C i)
    · intro i
      exact (((harrisIntegralAdeleStabilizer D C).inv_mem hg) _).mpr
        (sourceBasis_mem D C i)
  · rintro ⟨hf, hi⟩ v
    constructor
    · intro hv
      have h := sourceSpan_map_mem D C
        (ScalarExtensionSimilitudePoints.operator g).symm.toLinearMap hi hv
      simpa only [LinearEquiv.coe_coe, ScalarExtensionSimilitudePoints.operator_symm_apply,
        LinearEquiv.symm_apply_apply] using h
    · intro hv
      exact sourceSpan_map_mem D C
        (ScalarExtensionSimilitudePoints.operator g).toLinearMap hf hv

/-- The actual source-lattice stabilizer is open in the original similitude topology. -/
theorem harrisIntegralAdeleStabilizer_isOpen :
    IsOpen (X := G) {g : G | g ∈ harrisIntegralAdeleStabilizer D C} := by
  have heq : {g : G | g ∈ harrisIntegralAdeleStabilizer D C} =
      (⋂ i, {g : G | g.val.1 ((1 : Af) ⊗ₜ[ℚ] sourceRationalBasis D C i) ∈ Λf}) ∩
      (⋂ i, {g : G | g.val.1.symm ((1 : Af) ⊗ₜ[ℚ] sourceRationalBasis D C i) ∈ Λf}) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred]
    exact stabilizer_mem_iff D C g
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact (harrisHodgePELIntegralAdeleSpan_isOpen D C).preimage
      (ScalarExtensionSimilitudePoints.continuous_apply _)
  · apply isOpen_iInter_of_finite
    intro i
    exact (harrisHodgePELIntegralAdeleSpan_isOpen D C).preimage
      (ScalarExtensionSimilitudePoints.continuous_symm_apply _)

/-- The existing source stabilizer equipped with its proved openness. -/
def harrisIntegralAdeleOpenStabilizer : OpenSubgroup G where
  toSubgroup := harrisIntegralAdeleStabilizer D C
  isOpen' := harrisIntegralAdeleStabilizer_isOpen D C

/-- Intersect any original compact-open level with the actual integral source stabilizer. -/
def harrisIntegralSourceRefinement
    (K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)) :
    FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C) where
  openSubgroup := K.openSubgroup ⊓ harrisIntegralAdeleOpenStabilizer D C
  isCompact := by
    let : Module.Finite ℚ A := Module.Finite.of_basis (sourceRationalBasis D C)
    exact K.isCompact.inter_right (harrisIntegralAdeleOpenStabilizer D C).isClosed

@[simp] theorem harrisIntegralSourceRefinement_mem
    (K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)) (g : G) :
    g ∈ (harrisIntegralSourceRefinement D C K).subgroup ↔
      g ∈ K.subgroup ∧ g ∈ harrisIntegralAdeleStabilizer D C := Iff.rfl

theorem harrisIntegralSourceRefinement_le
    (K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)) :
    (harrisIntegralSourceRefinement D C K).toSubgroup ≤ K.toSubgroup :=
  fun _ hg => hg.1

theorem harrisIntegralSourceRefinement_le_stabilizer
    (K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)) :
    (harrisIntegralSourceRefinement D C K).toSubgroup ≤
      harrisIntegralAdeleStabilizer D C := fun _ hg => hg.2

/-- The refinement has the original level-forgetting arrow, represented by the identity. -/
def harrisIntegralSourceRefinementArrow
    (K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)) :
    CompactOpenLevel.Arrow (harrisIntegralSourceRefinement D C K) K :=
  CompactOpenLevel.inclusion (harrisIntegralSourceRefinement_le D C K)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
