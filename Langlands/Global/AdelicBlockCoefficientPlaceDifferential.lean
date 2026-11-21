import Langlands.Global.AdelicBlockCoefficientDifferential
import Langlands.Global.AdelicBlockParabolicPlaceCurves
import Langlands.Automorphic.ArchimedeanPlaceOperatorFamily
import Langlands.Representation.Tensor.FiniteSlotDensity

/-! # Coefficient differentiation in the Lie algebra of one infinite place -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 210000
set_option Elab.async false

universe u v w

namespace Langlands.FiniteTensor

/-- A one-slot tensor endomorphism acts by the selected operator and identities elsewhere. -/
theorem slotAlgebraHom_eq_map_ite {I : Type v} [DecidableEq I] {V : I → Type w}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (i : I) (D : ∀ j, Module.End ℂ (V j)) :
    slotAlgebraHom i (D i) = PiTensorProduct.map (fun j => if j = i then D j else LinearMap.id) := by
  change PiTensorProduct.map (slot i (D i)) = _
  apply congrArg (PiTensorProduct.map (R := ℂ))
  funext j
  by_cases hj : j = i
  · subst j
    simp only [slot, Function.update_self, ite_true]
  · simp only [slot, Function.update_of_ne hj, ite_eq_right hj]

end Langlands.FiniteTensor

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear InfinitePlaceFamily NumberField ArchimedeanGL
open AdelicBlockDeterminantCharacter AdelicBlockParabolic ArchimedeanCompactBlocks

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i, OperatorRealization F (B.size i))

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup _

local notation "W" => coefficientValues F B S
local notation "E" => coefficientEquiv F B S

/-- The sum of the specified one-place Lie operators on the actual block coefficients. -/
def coefficientPlaceDifferential (p : Index F) (Y : ∀ i, Lie (B.size i) p) : Module.End ℂ W :=
  (E).toLinearMap.comp
    ((∑ i, FiniteTensor.slotAlgebraHom i ((S i).placeLieFamily p (Y i))).comp (E).symm.toLinearMap)

theorem coefficientPlaceDifferential_coefficientEquiv (p : Index F) (Y : ∀ i, Lie (B.size i) p)
    (x : ⨂[ℂ] i, (S i).Space) :
    coefficientPlaceDifferential F B S p Y (E x) =
      E ((∑ i, FiniteTensor.slotAlgebraHom i ((S i).placeLieFamily p (Y i))) x) := by
  simp only [coefficientPlaceDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

private theorem coefficientDifferential_eq_of_inclusions (p : Index F) (Y : ∀ i, Lie (B.size i) p)
    (X : ArchimedeanMatrix F n) (hY : ∀ i,
      complexify F (B.size i) ((realLieAlgebraToMatrix F (B.size i)).symm
        (archimedeanDiagonalBlock F B i X)) = lieInclusion (B.size i) p (Y i)) :
    coefficientDifferential F B S X = coefficientPlaceDifferential F B S p Y := by
  let A (i : Fin B.length) : Module.End ℂ (S i).Space :=
    (S i).envelopingAction (envelopingGenerator F (B.size i)
      (complexify F (B.size i) ((realLieAlgebraToMatrix F (B.size i)).symm
        (archimedeanDiagonalBlock F B i X))))
  let D (i : Fin B.length) : Module.End ℂ (S i).Space := (S i).placeLieFamily p (Y i)
  have hAD : A = D := funext fun i => congrArg ((S i).envelopingAction ∘ envelopingGenerator F (B.size i)) (hY i)
  have hsum : (∑ i, PiTensorProduct.map (fun j => if j = i then A j else LinearMap.id)) =
      ∑ i, FiniteTensor.slotAlgebraHom i (D i) := by
    rw [hAD]
    exact Finset.sum_congr rfl fun i _ => (FiniteTensor.slotAlgebraHom_eq_map_ite i D).symm
  exact congrArg (fun M : Module.End ℂ (⨂[ℂ] i, (S i).Space) =>
    (E).toLinearMap.comp (M.comp (E).symm.toLinearMap)) hsum

/-- The real-place tangent gives the Lie directions obtained by taking its diagonal blocks. -/
theorem coefficientDifferential_realPlace (v : {v : InfinitePlace F // v.IsReal})
    (X : Matrix (Fin n) (Fin n) ℝ) :
    coefficientDifferential F B S (realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X)) =
      coefficientPlaceDifferential F B S (.inl v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i X) := by
  apply coefficientDifferential_eq_of_inclusions F B S
  intro i
  rw [archimedeanDiagonalBlock_realPlaceLieInclusion, LinearEquiv.symm_apply_apply]
  exact (realPlaceComplexLieInclusion_tmul F (B.size i) v 1 (localDiagonalBlock ℝ B i X)).symm

/-- The complex-place tangent gives the Lie directions obtained by taking its diagonal blocks. -/
theorem coefficientDifferential_complexPlace (v : {v : InfinitePlace F // v.IsComplex})
    (X : Matrix (Fin n) (Fin n) ℂ) :
    coefficientDifferential F B S (realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X)) =
      coefficientPlaceDifferential F B S (.inr v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i X) := by
  apply coefficientDifferential_eq_of_inclusions F B S
  intro i
  rw [archimedeanDiagonalBlock_complexPlaceLieInclusion, LinearEquiv.symm_apply_apply]
  exact (complexPlaceComplexLieInclusion_tmul F (B.size i) v 1 (localDiagonalBlock ℂ B i X)).symm

end Langlands.Global.AdelicBlockScalarSections
