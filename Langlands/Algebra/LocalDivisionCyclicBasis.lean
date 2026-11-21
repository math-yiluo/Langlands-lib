import Langlands.Algebra.LocalDivisionDegree
import Langlands.Algebra.LocalDivisionReducedDegree
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # A cyclic basis for the actual local division algebra -/

noncomputable section

namespace Langlands.CentralDivision

open Module

universe u s

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L]
  (ι : L →ₐ[K] D)

local notation "d" => CentralSimple.reducedDegree K D

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
private theorem cyclicBasisScalarTower :
    letI := localDivisionSubfieldLeftModule K D ι
    IsScalarTower K L D := by
  let := localDivisionSubfieldLeftModule K D ι
  exact ⟨fun k l x => by
    change ι (k • l) * x = k • (ι l * x)
    rw [map_smul, smul_mul_assoc]⟩

variable {σ : L ≃ₐ[K] L} {j : Dˣ}
variable (hconj : ∀ a : L, (j : D) * ι a = ι (σ a) * (j : D))

include hconj in
omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- Powers of the implementing unit move the coefficients by the same powers
of the field automorphism. -/
theorem implementingUnit_pow_mul (n : ℕ) (a : L) :
    (j : D) ^ n * ι a = ι ((σ ^ n) a) * (j : D) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (σ ^ (n + 1)) a = σ ((σ ^ n) a) := by rw [pow_succ', AlgEquiv.mul_apply]
    rw [hs, pow_succ', mul_assoc, ih, ← mul_assoc, hconj, mul_assoc]

variable [FiniteDimensional K L]
  (hdegree : Module.finrank K L = CentralSimple.reducedDegree K D)

include hdegree in
private theorem cyclicBasis_finrank :
    letI := localDivisionSubfieldLeftModule K D ι
    Module.finrank L D = d := by
  let := localDivisionSubfieldLeftModule K D ι
  let := cyclicBasisScalarTower K D ι
  let : FiniteDimensional L D := Module.Finite.of_restrictScalars_finite K L D
  have h := Module.finrank_mul_finrank K L D
  rw [hdegree, CentralSimple.finrank_eq_reducedDegree_mul_self K D] at h
  exact Nat.eq_of_mul_eq_mul_left (CentralSimple.reducedDegree_pos K D) h

variable [IsGalois K L] (horder : orderOf σ = CentralSimple.reducedDegree K D)

include horder hconj in
omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
private theorem linearIndependent_implementingUnit_pow :
    letI := localDivisionSubfieldLeftModule K D ι
    LinearIndependent L (fun i : Fin d => (j : D) ^ i.val) := by
  let := localDivisionSubfieldLeftModule K D ι
  obtain ⟨a, ha⟩ := Field.exists_primitive_element K L
  let m : Module.End L D :=
    { toFun := fun x => x * ι a
      map_add' := fun x y => add_mul x y (ι a)
      map_smul' := fun c x => by
        change (ι c * x) * ι a = ι c * (x * ι a)
        exact mul_assoc _ _ _ }
  let μ : Fin d → L := fun i => (σ ^ i.val) a
  have hμ : Function.Injective μ := by
    intro i k h
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := σ)
    · simpa only [Set.mem_Iio, horder] using i.isLt
    · simpa only [Set.mem_Iio, horder] using k.isLt
    apply AlgEquiv.coe_toAlgHom_injective
    let b := PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral (R := K) a) ha
    apply b.algHom_ext
    rw [show b.gen = a from PowerBasis.ofAdjoinSimpleEqTop_gen _ _]
    exact h
  apply m.eigenvectors_linearIndependent' μ hμ
  intro i
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, pow_ne_zero _ j.ne_zero⟩
  exact implementingUnit_pow_mul K D ι hconj i.val a

/-- The powers from zero to `d - 1` of the unit implementing a Galois
generator form a basis over the original embedded field acting on the left. -/
def implementingUnitBasis :
    letI := localDivisionSubfieldLeftModule K D ι
    Basis (Fin d) L D :=
  letI := localDivisionSubfieldLeftModule K D ι
  letI := cyclicBasisScalarTower K D ι
  letI : FiniteDimensional L D := Module.Finite.of_restrictScalars_finite K L D
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_implementingUnit_pow K D ι hconj horder)
    (by rw [Fintype.card_fin, cyclicBasis_finrank K D ι hdegree])

@[simp]
theorem implementingUnitBasis_apply (i : Fin d) :
    letI := localDivisionSubfieldLeftModule K D ι
    implementingUnitBasis K D ι hconj hdegree horder i = (j : D) ^ i.val := by
  let := localDivisionSubfieldLeftModule K D ι
  let := cyclicBasisScalarTower K D ι
  let : FiniteDimensional L D := Module.Finite.of_restrictScalars_finite K L D
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

include hconj hdegree horder in
private theorem implementingUnit_pow_reducedDegree_mem_center :
    (j : D) ^ d ∈ Subalgebra.center K D := by
  let := localDivisionSubfieldLeftModule K D ι
  let b := implementingUnitBasis K D ι hconj hdegree horder
  have htriv : σ ^ d = 1 := horder ▸ pow_orderOf_eq_one σ
  apply Subalgebra.mem_center_iff.mpr
  intro x
  rw [← b.sum_repr x]
  apply Commute.sum_left
  intro i _
  change Commute (ι (b.repr x i) * b i) ((j : D) ^ d)
  have hcoeff : Commute (ι (b.repr x i)) ((j : D) ^ d) := by
    symm
    change (j : D) ^ d * ι (b.repr x i) = ι (b.repr x i) * (j : D) ^ d
    rw [implementingUnit_pow_mul K D ι hconj, htriv, AlgEquiv.one_apply]
  have hpower : Commute (b i) ((j : D) ^ d) := by
    change Commute (implementingUnitBasis K D ι hconj hdegree horder i) ((j : D) ^ d)
    rw [implementingUnitBasis_apply]
    exact Commute.pow_pow_self _ _ _
  exact hcoeff.mul_left hpower

include hconj hdegree horder in
private theorem implementingUnit_pow_reducedDegree_exists_scalar :
    ∃ a : K, algebraMap K D a = (j : D) ^ d := by
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).mp
    (implementingUnit_pow_reducedDegree_mem_center K D ι hconj hdegree horder)
  exact ⟨a, ha.symm⟩

/-- The actual central parameter of the cyclic presentation, represented as a
base-field unit whose image is the reduced-degree power of the implementing unit. -/
def cyclicParameter : Kˣ :=
  let hs := implementingUnit_pow_reducedDegree_exists_scalar K D ι hconj hdegree horder
  Units.mk0 hs.choose (by
    intro hzero
    have hmap := hs.choose_spec
    rw [hzero, map_zero] at hmap
    exact pow_ne_zero _ j.ne_zero hmap.symm)

@[simp]
theorem algebraMap_cyclicParameter :
    algebraMap K D (cyclicParameter K D ι hconj hdegree horder : K) = (j : D) ^ d :=
  (implementingUnit_pow_reducedDegree_exists_scalar K D ι hconj hdegree horder).choose_spec

end Langlands.CentralDivision
