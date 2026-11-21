import Langlands.Algebra.LocalDivisionCyclicChartLifts
import Langlands.Algebra.BrauerComparison.Relative
import Langlands.ClassFieldTheory.Local.CyclicCupArtinComparison

/-! # The carry cocycle of the opposite division splitting chart -/

noncomputable section

namespace Langlands.CentralDivision

open Module Matrix BrauerComparison CentralSimple CentralSimple.SemilinearGaloisAction ClassFieldTheory.Local
open scoped TensorProduct MatrixGroups

attribute [local instance] coefficientGLAction

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L]
  (ι : L →ₐ[K] D)
  (b : letI := localDivisionSubfieldLeftModule K D ι
       Basis (Fin (CentralSimple.reducedDegree K D)) L D)
  {σ : L ≃ₐ[K] L} {j : Dˣ}
  (hj : ∀ a : L, (j : D) * ι a = ι (σ a) * (j : D))

local notation "nD" => CentralSimple.reducedDegree K D
local notation "Idx" => Fin nD
local notation "Vec" => (Idx → L)

local instance cyclicCarryDegreeNonzero : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(CentralSimple.reducedDegree_pos K D).ne'⟩

variable (χ : (L ≃ₐ[K] L) ≃* Multiplicative (ZMod (CentralSimple.reducedDegree K D)))

/-- Lift a Galois element by the power corresponding to its standard cyclic
representative. -/
def subfieldCyclicCarryLift (g : L ≃ₐ[K] L) : GL Idx L :=
  subfieldCyclicPowerLift K D ι b hj (χ g).toAdd.val

variable [FiniteDimensional K L] [IsGalois K L]
  (hdegree : Module.finrank K L = CentralSimple.reducedDegree K D)
  (horder : orderOf σ = CentralSimple.reducedDegree K D)

local notation "parameter" => cyclicParameter K D ι hj hdegree horder

include horder hdegree in
private theorem subfieldCyclicPowerLift_period (k m : ℕ) :
    (subfieldCyclicPowerLift K D ι b hj (nD * k + m) : Matrix Idx Idx L) =
      Matrix.scalar Idx (algebraMap K L ((parameter : K) ^ k)) *
        (subfieldCyclicPowerLift K D ι b hj m : Matrix Idx Idx L) := by
  let := localDivisionSubfieldLeftModule K D ι
  have htriv : σ ^ nD = 1 := horder ▸ pow_orderOf_eq_one σ
  have hσ : σ ^ (nD * k + m) = σ ^ m := by
    rw [pow_add, pow_mul, htriv, one_pow, one_mul]
  have hjpow : (j : D) ^ (nD * k + m) =
      ι (algebraMap K L ((parameter : K) ^ k)) * (j : D) ^ m := by
    rw [pow_add, pow_mul, ι.commutes, map_pow, algebraMap_cyclicParameter]
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  let s := σ ^ m
  have hsurj : Function.Surjective (fun x : D => s ∘ b.equivFun x) :=
    (Equiv.piCongrRight (fun _ : Idx => s.toEquiv)).surjective.comp b.equivFun.surjective
  obtain ⟨x, rfl⟩ := hsurj v
  change (subfieldCyclicPowerLift K D ι b hj (nD * k + m) : Matrix Idx Idx L) *ᵥ (s ∘ b.repr x) = _
  have hl := subfieldCyclicPowerLift_mulVec K D ι b hj (nD * k + m) x
  rw [hσ] at hl
  rw [hl, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mulVec]
  change (b.repr ((j : D) ^ (nD * k + m) * x) : Vec) =
    algebraMap K L ((parameter : K) ^ k) •
      ((subfieldCyclicPowerLift K D ι b hj m : Matrix Idx Idx L) *ᵥ (s ∘ b.repr x))
  rw [subfieldCyclicPowerLift_mulVec K D ι b hj m x, hjpow, mul_assoc]
  exact b.equivFun.map_smul (algebraMap K L ((parameter : K) ^ k)) ((j : D) ^ m * x)

variable (hχ : cyclicCoordinateGenerator χ = σ)

include hχ horder hdegree in
/-- Multiplication of the chosen cyclic lifts has the positive carry factor
from the actual base-field parameter. -/
theorem subfieldCyclicCarryLift_mul (g h : L ≃ₐ[K] L) :
    subfieldCyclicCarryLift K D ι b hj χ g * (g • subfieldCyclicCarryLift K D ι b hj χ h) =
      GeneralLinearGroup.scalar Idx
        ((Units.map (algebraMap K L).toMonoidHom parameter) ^
          cyclicCarry (χ g).toAdd (χ h).toAdd) * subfieldCyclicCarryLift K D ι b hj χ (g * h) := by
  let i := (χ g).toAdd.val
  let k := (χ h).toAdd.val
  let p := (χ (g * h)).toAdd.val
  let c := cyclicCarry (χ g).toAdd (χ h).toAdd
  have hg : σ ^ i = g := hχ ▸ cyclicCoordinateGenerator_pow_val χ g
  have hi : i + k = nD * c + p := by
    simpa only [i, k, c, p, map_mul, toAdd_mul] using (cyclicCarry_spec (χ g).toAdd (χ h).toAdd).symm
  have hmul := subfieldCyclicPowerLift_mul K D ι b hj i k
  rw [hg] at hmul
  apply Units.ext
  simp only [Units.val_mul, coefficientGLAction_coe, GeneralLinearGroup.coe_scalar,
    Units.val_pow_eq_pow_val, Units.coe_map]
  change (subfieldCyclicPowerLift K D ι b hj i : Matrix Idx Idx L) *
      (subfieldCyclicPowerLift K D ι b hj k : Matrix Idx Idx L).map g =
    Matrix.scalar Idx ((algebraMap K L (parameter : K)) ^ c) *
      (subfieldCyclicPowerLift K D ι b hj p : Matrix Idx Idx L)
  rw [hmul, hi, ← map_pow]
  exact subfieldCyclicPowerLift_period K D ι b hj hdegree horder c p

include hχ hdegree horder in
/-- The relative class of the actual opposite splitting chart is the positive
carry class of the cyclic parameter. -/
theorem subfieldOppositeSplittingChart_relativeClass :
    relativeClass (subfieldOppositeSplittingChart K D ι b) =
      cyclicClass K L χ.toMonoidHom parameter := by
  let P := subfieldCyclicCarryLift K D ι b hj χ
  let c : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ := fun g h =>
    (Units.map (algebraMap K L).toMonoidHom parameter) ^ cyclicCarry (χ g).toAdd (χ h).toAdd
  let ρ := splittingChartIndexAction (subfieldOppositeSplittingChart K D ι b)
  have hact (g : L ≃ₐ[K] L) (X : Matrix Idx Idx L) : ρ.act g X =
      (P g : Matrix Idx Idx L) * X.map g * (((P g)⁻¹ : GL Idx L) : Matrix Idx Idx L) := by
    let i := (χ g).toAdd.val
    have hg : σ ^ i = g := hχ ▸ cyclicCoordinateGenerator_pow_val χ g
    have h := subfieldCyclicPowerLift_chartAction K D ι b hj i X
    rw [hg] at h
    exact h
  change descentClass ρ = _
  rw [descentClass_eq_of_lifts ρ P c hact
    (subfieldCyclicCarryLift_mul K D ι b hj χ hdegree horder hχ)]
  unfold unitClass cyclicClass
  congr 1

end Langlands.CentralDivision
