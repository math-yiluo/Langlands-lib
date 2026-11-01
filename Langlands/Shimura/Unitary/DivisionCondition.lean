import Langlands.Shimura.Unitary.CMData
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Algebra.GroupWithZero.Action.Units

/-! # The division condition and the regular-module dimension obstruction -/

noncomputable section

universe u v w z

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [NumberField E] [IsScalarTower E K A]

/-- The extra division-algebra condition, imposed on the actual underlying ring.
Central simplicity alone does not supply it. -/
def IsDivision (_D : CentralSimpleUnitaryData E K A n) : Prop :=
  ∀ a : A, a ≠ 0 → IsUnit a

/-- For this nontrivial algebra, division is exactly simplicity of the actual
left regular module. -/
theorem isDivision_iff_isSimpleModule : D.IsDivision ↔ IsSimpleModule A A := by
  have : Nontrivial A := Module.nontrivial_of_finrank_pos (R := K) (by
    rw [D.dimension]
    have := D.rank_gt_one
    positivity)
  constructor
  · intro h
    exact isSimpleModule_self_iff_isUnit.mpr ⟨inferInstance, h⟩
  · intro h
    exact (isSimpleModule_self_iff_isUnit.mp h).2

/-- Passing from the algebra to its opposite preserves the division condition.
This retains the right-regular convention in the PEL construction. -/
theorem isDivision_iff_opposite :
    D.IsDivision ↔ ∀ a : Aᵐᵒᵖ, a ≠ 0 → IsUnit a := by
  constructor
  · intro h a ha
    exact (h a.unop (by simpa using ha)).op
  · intro h a ha
    exact (h (MulOpposite.op a) (by simpa using ha)).unop

variable [Algebra ℚ A]
  {M : Type z} [AddCommGroup M] [Module A M] [Module ℚ M]
  [IsScalarTower ℚ A M]

/-- The actual rational linear map sending an algebra element to its action
on a fixed vector. -/
def regularOrbitLinearMap (_D : CentralSimpleUnitaryData E K A n)
    (m : M) : A →ₗ[ℚ] M where
  toFun a := a • m
  map_add' a b := add_smul a b m
  map_smul' r a := smul_assoc r a m

@[simp] theorem regularOrbitLinearMap_apply (m : M) (a : A) :
    D.regularOrbitLinearMap m a = a • m := rfl

/-- A nonzero vector in a module over the division algebra gives an injection
of the whole regular module, with its rational scalar structure. -/
theorem regularOrbitLinearMap_injective (hD : D.IsDivision) {m : M} (hm : m ≠ 0) :
    Function.Injective (D.regularOrbitLinearMap m) := by
  intro a b hab
  change a • m = b • m at hab
  by_contra hne
  have hz : (a - b) • m = 0 := by rw [sub_smul, hab, sub_self]
  exact hm ((hD (a - b) (sub_ne_zero.mpr hne)).smul_eq_zero.mp hz)

/-- Every nonzero module of finite rational dimension has dimension at least
that of the actual division algebra. -/
theorem finrank_le_of_nonzero (hD : D.IsDivision) [Module.Finite ℚ M]
    {m : M} (hm : m ≠ 0) :
    Module.finrank ℚ A ≤ Module.finrank ℚ M :=
  LinearMap.finrank_le_finrank_of_injective
    (D.regularOrbitLinearMap_injective hD hm)

/-- A module of smaller rational dimension must be zero. This is the linear
obstruction used to exclude a nonzero torus character module in the source's
properness argument. It does not construct a Neron model or a torus. -/
theorem eq_zero_of_finrank_lt (hD : D.IsDivision) [Module.Finite ℚ M]
    (hM : Module.finrank ℚ M < Module.finrank ℚ A) (m : M) : m = 0 := by
  by_contra hm
  exact (not_le.mpr hM) (D.finrank_le_of_nonzero hD hm)

theorem subsingleton_of_finrank_lt (hD : D.IsDivision) [Module.Finite ℚ M]
    (hM : Module.finrank ℚ M < Module.finrank ℚ A) : Subsingleton M :=
  ⟨fun x y => (D.eq_zero_of_finrank_lt hD hM x).trans
    (D.eq_zero_of_finrank_lt hD hM y).symm⟩

end Langlands.Shimura.CentralSimpleUnitaryData
