import Langlands.GroupScheme.Lie.TorusRegularElement
import Langlands.GroupScheme.Lie.CocharacterTangent
import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.AffineBracketFunctoriality
import Langlands.GroupScheme.Lie.FieldAlgebraLie
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Lie.Weights.Basic

/-! # Algebraic torus weights and adjoint Lie weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Langlands.GroupScheme.Lie.FieldLie

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Lie

section Decomposition

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  {H : LieSubalgebra k L} {Index : Type*} [DecidableEq Index] (W : Index → Submodule k L)
  (weight : Index → H → k)
  (hW : ∀ a (x : L), x ∈ W a → ∀ Y : H, ⁅(Y : L), x⁆ = weight a Y • x)

include hW

private theorem weightComponent_eq_zero (hSpans : DirectSum.IsInternal W)
    {χ : H → k} {x : L} (hx : x ∈ LieModule.weightSpace L χ)
    {a : Index} (ha : weight a ≠ χ) :
    letI := hSpans.chooseDecomposition
    DirectSum.decompose W x a = 0 := by
  classical
  let _ := hSpans.chooseDecomposition
  obtain ⟨Y, hY⟩ := Function.ne_iff.mp ha
  let projection := (DirectSum.component k Index (fun b => W b) a).comp
    (DirectSum.decomposeLinearEquiv W).toLinearMap
  have hmap : projection.comp (LieModule.toEnd k H L Y) = weight a Y • projection := by
    apply DirectSum.decompose_lhom_ext W
    intro b
    apply LinearMap.ext
    intro y
    change projection ⁅(Y : L), (y : L)⁆ = weight a Y • projection y
    rw [hW b y y.property Y, map_smul]
    by_cases hba : b = a
    · subst b
      rfl
    · have hzero : projection (y : L) = 0 := by
        change DirectSum.component k Index (fun b => W b) a
          (DirectSum.decomposeLinearEquiv W (y : L)) = 0
        rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.component.of, dite_eq_right hba]
      rw [hzero, smul_zero, smul_zero]
  have he : projection ⁅(Y : L), x⁆ = weight a Y • projection x := LinearMap.congr_fun hmap x
  have hxY : ⁅(Y : L), x⁆ = χ Y • x := (LieModule.mem_weightSpace χ x).mp hx Y
  rw [hxY, map_smul] at he
  have hdiff : (weight a Y - χ Y) • projection x = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hY)

private theorem adjointWeightSpace_eq_of_decomposition
    (hSpans : DirectSum.IsInternal W) (hweight : Function.Injective weight) (a : Index) :
    (LieModule.weightSpace L (weight a)).toSubmodule = W a := by
  classical
  let _ := hSpans.chooseDecomposition
  apply le_antisymm
  · intro x hx
    let y := DirectSum.decompose W x a
    suffices hxy : x = (y : L) from hxy ▸ y.property
    apply (DirectSum.decomposeLinearEquiv W).injective
    rw [DirectSum.decomposeLinearEquiv_apply_coe]
    apply DirectSum.ext_component k
    intro b
    change DirectSum.decompose W x b =
      DirectSum.component k Index (fun c => W c) b (DirectSum.lof k Index (fun c => W c) a y)
    by_cases hab : a = b
    · subst b
      exact (DirectSum.component.lof_self (M := fun c => ↥(W c)) k a y).symm
    · rw [DirectSum.component.of, dite_eq_right hab]
      exact weightComponent_eq_zero W weight hW hSpans hx (fun h => hab (hweight h).symm)
  · intro x hx
    exact (LieModule.mem_weightSpace (weight a) x).mpr (hW a x hx)

private theorem exists_adjointWeight_of_ne_bot
    (hSpans : DirectSum.IsInternal W) {χ : H → k}
    (hχ : LieModule.weightSpace L χ ≠ ⊥) : ∃ a, weight a = χ := by
  classical
  by_contra hex
  let _ := hSpans.chooseDecomposition
  apply hχ
  apply LieSubmodule.toSubmodule_injective
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply (DirectSum.decomposeLinearEquiv W).injective
  rw [map_zero]
  apply DirectSum.ext_component k
  intro a
  rw [map_zero]
  exact weightComponent_eq_zero W weight hW hSpans hx (fun h => hex ⟨a, h⟩)

end Decomposition

section Torus

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom T.toGrp.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom]

local notation "L" => Additive (lieKernel G k)
local notation "H" => LieHom.range (targetMapLieHom i k)

/-- The differential of a torus character, evaluated on the image of the torus Lie
algebra in the ambient Lie algebra. -/
def torusWeightDifferential (χ : characterLattice T) (Y : H) : k :=
  (characterValue χ ((LinearEquiv.ofInjective (targetMapLinear i k)
    (targetMapLinear_injective i k)).symm Y).toMul.val : DualNumber k).snd

theorem torusWeightDifferential_targetMap (χ : characterLattice T)
    (Y : Additive (lieKernel T.toGrp k)) :
    torusWeightDifferential i χ ⟨targetMapLinear i k Y, ⟨Y, rfl⟩⟩ =
      (characterValue χ Y.toMul.val : DualNumber k).snd := by
  let e := LinearEquiv.ofInjective (targetMapLinear i k) (targetMapLinear_injective i k)
  change (characterValue χ (e.symm (e Y)).toMul.val : DualNumber k).snd = _
  rw [e.symm_apply_apply]

@[simp] theorem torusWeightDifferential_cocharacter (χ : characterLattice T)
    (ν : cocharacterLattice T) :
    torusWeightDifferential i χ
        ⟨targetMapLinear i k (Additive.ofMul (cocharacterTangent ν)), ⟨_, rfl⟩⟩ =
      (latticePairing T χ ν : k) := by
  rw [torusWeightDifferential_targetMap, toMul_ofMul, characterValue_cocharacterTangent_snd]

@[simp] theorem torusWeightDifferential_zero : torusWeightDifferential i 0 = 0 := by
  funext Y
  simp [torusWeightDifferential, characterValue_zero]

/-- Over a characteristic-zero field the adjoint Lie weight determines the split
torus character. -/
theorem torusWeightDifferential_injective [CharZero k] (hT : IsSplitTorus T.toGrp) :
    Function.Injective (torusWeightDifferential i) := by
  intro χ ψ h
  by_contra hne
  obtain ⟨n, hn, ν, hν⟩ := hT.exists_pairing_eq_pos (sub_ne_zero.mpr hne)
  have hpair : latticePairing T χ ν = latticePairing T ψ ν := by
    apply Int.cast_injective (α := k)
    simpa only [torusWeightDifferential_cocharacter] using
      congrFun h ⟨targetMapLinear i k (Additive.ofMul (cocharacterTangent ν)), ⟨_, rfl⟩⟩
  rw [map_sub, LinearMap.sub_apply, hpair, sub_self] at hν
  exact (Int.natCast_ne_zero.mpr hn.ne') hν.symm

variable [LocallyOfFiniteType G.X.hom]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- A character weight vector is a simultaneous adjoint eigenvector with the
differential of that character. -/
theorem mem_adjointWeightSpace_of_mem_torusWeightSpace {χ : characterLattice T}
    {x : L} (hx : x ∈ weightSpace i χ) :
    x ∈ LieModule.weightSpace L (torusWeightDifferential i χ) := by
  apply (LieModule.mem_weightSpace _ _).mpr
  intro Y
  obtain ⟨y, hy⟩ := Y.property
  have hy' : Y = ⟨targetMapLinear i k y, ⟨y, rfl⟩⟩ := Subtype.ext hy.symm
  rw [hy', torusWeightDifferential_targetMap]
  let c := finiteCoordinates G
  apply (c.equiv (.of _ k)).injective
  change c.equiv (.of _ k) ⁅targetMapLinear i k y, x⁆ =
    c.equiv (.of _ k) ((characterValue χ y.toMul.val : DualNumber k).snd • x)
  rw [← adjointDifferentialLieHom_apply_bracket, map_smul]
  exact adjointDifferentialFamily_targetMap_of_mem_weightSpace c i hx y.toMul

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- The algebraic character weight space and its differentiated adjoint weight
space coincide for a split torus in characteristic zero. -/
theorem adjointWeightSpace_eq_torusWeightSpace [CharZero k] (hT : IsSplitTorus T.toGrp)
    (χ : characterLattice T) :
    (LieModule.weightSpace L (torusWeightDifferential i χ)).toSubmodule = weightSpace i χ := by
  classical
  exact adjointWeightSpace_eq_of_decomposition (weightSpace i) (torusWeightDifferential i)
    (fun ψ x hx => (LieModule.mem_weightSpace (torusWeightDifferential i ψ) x).mp
      (mem_adjointWeightSpace_of_mem_torusWeightSpace i hx))
    (isInternal_weightSpace_of_isSplitTorus k G T hT i)
    (torusWeightDifferential_injective i hT) χ

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- Every nonzero adjoint weight space of a split torus differential comes from
an algebraic character of that torus. -/
theorem exists_torusWeightDifferential_of_ne_bot (hT : IsSplitTorus T.toGrp)
    {χ : H → k} (hχ : LieModule.weightSpace L χ ≠ ⊥) :
    ∃ ψ, torusWeightDifferential i ψ = χ := by
  classical
  exact exists_adjointWeight_of_ne_bot (weightSpace i) (torusWeightDifferential i)
    (fun ψ x hx => (LieModule.mem_weightSpace (torusWeightDifferential i ψ) x).mp
      (mem_adjointWeightSpace_of_mem_torusWeightSpace i hx))
    (isInternal_weightSpace_of_isSplitTorus k G T hT i) hχ

end Torus

end Langlands.GroupScheme.Lie
