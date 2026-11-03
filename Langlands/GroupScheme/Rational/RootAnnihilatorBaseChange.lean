import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Real scalar extension of integral character annihilators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

private def rootEvaluationInt (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (J : Set (characterLattice T)) : cocharacterLattice T →ₗ[ℤ] (J → ℤ) :=
  LinearMap.pi fun α => latticePairing T α.1

/-- The integral cocharacters annihilated by every selected actual character. -/
def rootAnnihilatorInt (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (J : Set (characterLattice T)) : Submodule ℤ (cocharacterLattice T) :=
  (rootEvaluationInt T J).ker

@[simp] theorem mem_rootAnnihilatorInt (J : Set (characterLattice T))
    (ν : cocharacterLattice T) :
    ν ∈ rootAnnihilatorInt T J ↔ ∀ α ∈ J, latticePairing T α ν = 0 := by
  simp only [rootAnnihilatorInt, LinearMap.mem_ker, funext_iff,
    rootEvaluationInt, LinearMap.pi_apply, Pi.zero_apply]
  exact SetCoe.forall

private theorem rootEvaluationInt_baseChange (J : Set (characterLattice T)) :
    (piScalarRightHom ℤ ℝ ℝ J).comp ((rootEvaluationInt T J).baseChange ℝ) =
      LinearMap.pi (fun α : J => eval T α.1) := by
  apply AlgebraTensorModule.ext
  intro r ν
  ext α
  simp [rootEvaluationInt, mul_comm]

private theorem ker_rootEvaluationInt_baseChange (J : Set (characterLattice T))
    [Finite J] :
    ((rootEvaluationInt T J).baseChange ℝ).ker = rootAnnihilator T J := by
  classical
  let := Fintype.ofFinite J
  have hinj : Function.Injective (piScalarRightHom ℤ ℝ ℝ J) :=
    (piScalarRight ℤ ℝ ℝ J).injective
  rw [← LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr hinj), rootEvaluationInt_baseChange]
  ext v
  simp only [LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Pi.zero_apply,
    mem_rootAnnihilator]
  exact SetCoe.forall

/-- Real scalar extension of the integral common annihilator is exactly the
published real common annihilator, for a finite character selection. -/
theorem rootAnnihilatorInt_baseChange (J : Set (characterLattice T)) [Finite J] :
    (rootAnnihilatorInt T J).baseChange ℝ = rootAnnihilator T J := by
  change LinearMap.range
    (AlgebraTensorModule.lTensor ℝ ℝ (rootEvaluationInt T J).ker.subtype) = _
  rw [← Module.Flat.ker_lTensor_eq ℝ ℝ (rootEvaluationInt T J)]
  exact ker_rootEvaluationInt_baseChange J

/-- The canonical real-linear equivalence from the scalar extension of the
integral common annihilator to the published real annihilator. -/
def rootAnnihilatorBaseChange (J : Set (characterLattice T)) [Finite J] :
    ℝ ⊗[ℤ] rootAnnihilatorInt T J ≃ₗ[ℝ] rootAnnihilator T J :=
  (LinearMap.tensorKerEquiv ℝ ℝ (rootEvaluationInt T J)).trans
    (LinearEquiv.ofEq _ _ (ker_rootEvaluationInt_baseChange J))

@[simp] theorem rootAnnihilatorBaseChange_coe (J : Set (characterLattice T))
    [Finite J] (x : ℝ ⊗[ℤ] rootAnnihilatorInt T J) :
    (rootAnnihilatorBaseChange J x : V T) =
      (rootAnnihilatorInt T J).subtype.baseChange ℝ x := by
  change (LinearMap.tensorKer ℝ ℝ (rootEvaluationInt T J) x : V T) = _
  exact LinearMap.tensorKer_coe ℝ ℝ (rootEvaluationInt T J) x

@[simp] theorem rootAnnihilatorBaseChange_tmul (J : Set (characterLattice T))
    [Finite J] (r : ℝ) (ν : rootAnnihilatorInt T J) :
    (rootAnnihilatorBaseChange J (r ⊗ₜ[ℤ] ν) : V T) = r ⊗ₜ[ℤ] ν.1 := by
  rw [rootAnnihilatorBaseChange_coe, LinearMap.baseChange_tmul]
  rfl

end Langlands.GroupScheme.RealTorusSpace
