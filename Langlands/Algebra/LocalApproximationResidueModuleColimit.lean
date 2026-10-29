import Langlands.Algebra.LocalApproximationResidueModuleColimitStatement
import Langlands.Algebra.LocalApproximationResidueInjectivity

/-! # Preservation of the actual residue-module colimit: proof -/

open scoped TensorProduct
open IsLocalRing
open scoped Langlands.Algebra.LocalModuleSystem

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra
namespace ResidueModuleColimitProof

open ResidueInjectivityProof

attribute [local instance] fieldAlgebra

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M)

section Comparison

/-- A raw residue fibre `κᵢ ⊗[Rᵢ] Mᵢ` sent into the fixed-field fibre `κ ⊗[Rᵢ] Mᵢ`: extend
scalars along `κᵢ → κ` by `x ↦ 1 ⊗ x`, then cancel the intermediate residue field. -/
noncomputable def residueToField (i : ι) (x : E.ResidueFiber i) : FieldFiber E i :=
  letI := (D.residueι i).toAlgebra
  residueExtensionEquiv E i ((1 : ResidueField R) ⊗ₜ[ResidueField (D.base i)] x)

theorem residueToField_tmul (i : ι) (b : ResidueField (D.base i)) (m : E.obj i) :
    residueToField E i (b ⊗ₜ[D.base i] m) = D.residueι i b ⊗ₜ[D.base i] m := by
  let := (D.residueι i).toAlgebra
  change (b • (1 : ResidueField R)) ⊗ₜ[D.base i] m = _
  rw [Algebra.smul_def, mul_one]
  rfl

theorem residueToField_add (i : ι) (x y : E.ResidueFiber i) :
    residueToField E i (x + y) = residueToField E i x + residueToField E i y := by
  let := (D.residueι i).toAlgebra
  simp only [residueToField, TensorProduct.tmul_add, map_add]

theorem residueToField_zero (i : ι) : residueToField E i 0 = 0 := by
  let := (D.residueι i).toAlgebra
  simp only [residueToField, TensorProduct.tmul_zero, map_zero]

theorem residueToField_injective (i : ι) : Function.Injective (residueToField E i) := by
  let := (D.residueι i).toAlgebra
  intro x y hxy
  exact includeResidue_injective E i ((residueExtensionEquiv E i).injective hxy)

/-- The comparison intertwines the actual residue transitions with the fixed-field ones. -/
theorem fieldFiberMap_residueToField {i j : ι} (h : i ≤ j) (x : E.ResidueFiber i) :
    fieldFiberMap E h (residueToField E i x) = residueToField E j (E.residueFiberMap h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    rw [residueToField_tmul, fieldFiberMap_tmul, LocalModuleSystem.residueFiberMap_tmul,
      residueToField_tmul, LocalAlgebraSystem.residueι_compat]
  | add x y hx hy => rw [residueToField_add, map_add, hx, hy, map_add, residueToField_add]

variable [Module R M] [IsScalarTower R S M]

/-- The comparison intertwines the actual residue cocone with the fixed-field cocone. -/
theorem fieldFiberι_residueToField (i : ι) (x : E.ResidueFiber i) :
    fieldFiberι E i (residueToField E i x) = E.residueFiberι i x := by
  let := (D.residueι i).toAlgebra
  rw [residueToField, ← residueFiberΨ_eq, LocalModuleSystem.residueFiberΨ_tmul, one_smul]

end Comparison

section Lift
variable [Module R M] [IsScalarTower R S M] [DecidableEq ι]

/-- Every element of `κ ⊗[R] M` comes from some stage of the residue-module system. -/
theorem lift_surjective (hE : E.IsColimit) :
    Function.Surjective (AddCommGroup.DirectLimit.lift E.ResidueFiber
      (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom)
      (LocalModuleSystem.TargetResidueFiber R M)
      (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
      (fun _ _ h x ↦ E.residueFiberι_compat h x)) := by
  obtain ⟨⟨hR, -⟩, hM⟩ := hE
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := residue_surjective a
    obtain ⟨i, r', rfl⟩ := exists_baseι_eq D hR.2 r
    obtain ⟨k, m', rfl⟩ := exists_ιM_eq E hM m
    obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
    refine ⟨AddCommGroup.DirectLimit.of E.ResidueFiber
      (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom) l
      (residue (D.base l) (D.baseMap i l hil r') ⊗ₜ[D.base l] E.map k l hkl m'), ?_⟩
    refine (AddCommGroup.DirectLimit.lift_of _ _ _ l _).trans ?_
    rw [LinearMap.toAddMonoidHom_coe, LocalModuleSystem.residueFiberι_tmul,
      LocalAlgebraSystem.residueι_residue, D.baseι_compat, E.ιM_compat]
  | add x y hx hy =>
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact ⟨z + w, map_add _ z w⟩

/-- An element of the residue-module direct limit with zero image in `κ ⊗[R] M` is zero. -/
theorem lift_injective (hE : E.IsColimit) :
    Function.Injective (AddCommGroup.DirectLimit.lift E.ResidueFiber
      (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom)
      (LocalModuleSystem.TargetResidueFiber R M)
      (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
      (fun _ _ h x ↦ E.residueFiberι_compat h x)) := by
  obtain ⟨⟨hR, -⟩, hM⟩ := hE
  rw [injective_iff_map_eq_zero]
  intro z
  refine AddCommGroup.DirectLimit.induction_on z (fun i x hx₀ ↦ ?_)
  have hx : E.residueFiberι i x = 0 :=
    (AddCommGroup.DirectLimit.lift_of _ _ _ i x).symm.trans hx₀
  obtain ⟨j, hij, hj⟩ := exists_fieldFiberMap_eq_zero E hM hR.2 (residueToField E i x)
    (by rw [fieldFiberι_residueToField, hx])
  have hx' : E.residueFiberMap hij x = 0 := by
    apply residueToField_injective E j
    rw [← fieldFiberMap_residueToField, hj, residueToField_zero]
  rw [← AddCommGroup.DirectLimit.of_f hij x, LinearMap.toAddMonoidHom_coe, hx', map_zero]

/-- The actual lift is bijective. -/
theorem lift_bijective (hE : E.IsColimit) :
    Function.Bijective (AddCommGroup.DirectLimit.lift E.ResidueFiber
      (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom)
      (LocalModuleSystem.TargetResidueFiber R M)
      (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
      (fun _ _ h x ↦ E.residueFiberι_compat h x)) :=
  ⟨lift_injective E hE, lift_surjective E hE⟩

end Lift
end ResidueModuleColimitProof

open ResidueModuleColimitProof in
/-- Preservation of the actual residue-module colimit for every directed local module system
with the given ring and module colimits. -/
theorem localApproximationResidueModuleColimit :
    LocalApproximationResidueModuleColimitStatement.{uI, uA, uB, uN, uR, uS, uM} := by
  intro ι _ _ _ R S _ _ _ _ _ _ D M _ _ _ _ E hE
  let := Classical.decEq ι
  exact lift_bijective E hE

end Langlands.Algebra
