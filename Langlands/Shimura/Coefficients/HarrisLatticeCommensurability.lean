import Langlands.Shimura.Coefficients.HarrisLatticeLevelInclusion
import Langlands.Shimura.Coefficients.LatticeCommensurability
import Mathlib.Algebra.Group.Pi.Units

/-! # Scalar comparisons in the original Harris coefficient module -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory Langlands.Global AdelicFunctoriality AlgebraInvolution
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
  {L : Type u} [Field L] [NumberField L]
  {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
  {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
  (p : FinitePlace ℚ) (U V : CompactOpenLevel σ.FiniteAdelicPoints)

/-- One integral scalar at each actual coefficient place bounds both original lattices. -/
def harrisLatticeComparisonScalar : HarrisCoefficientIntegers L p :=
  fun l => latticeComparisonScalar (K := FiniteCompletion L l.1)
    (algebraicCompactCoefficientLattice ρ p l.1 U).carrier
    (algebraicCompactCoefficientLattice ρ p l.1 V).carrier

theorem harrisLatticeComparisonScalar_component_ne_zero (l : FinitePlacesAbove L p) :
    harrisLatticeComparisonScalar ρ p U V l ≠ 0 :=
  latticeComparisonScalar_ne_zero _ _

/-- In the original tensor coefficient algebra the chosen product scalar is a unit. -/
theorem harrisLatticeComparisonScalar_isUnit :
    IsUnit (harrisCoefficientIntegersMap L p (harrisLatticeComparisonScalar ρ p U V)) := by
  apply (MulEquiv.isUnit_map (harrisCoefficientRingEquiv L p)).mp
  rw [harrisCoefficientRingEquiv_integers, Pi.isUnit_iff]
  intro l
  apply isUnit_iff_ne_zero.mpr
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero
      (harrisLatticeComparisonScalar_component_ne_zero ρ p U V l))

/-- Coordinate bounds give a bound in the whole product module. -/
theorem harrisProductLatticeComparisonScalar_forward
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)
    (hx : x ∈ harrisProductLattice ρ p U) :
    harrisLatticeComparisonScalar ρ p U V • x ∈ harrisProductLattice ρ p V := by
  intro l
  exact latticeComparisonScalar_forward _ _ (x l) (hx l)

theorem harrisProductLatticeComparisonScalar_backward
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)
    (hx : x ∈ harrisProductLattice ρ p V) :
    harrisLatticeComparisonScalar ρ p U V • x ∈ harrisProductLattice ρ p U := by
  intro l
  exact latticeComparisonScalar_backward _ _ (x l) (hx l)

/-- Transport the bound to the original tensor module, retaining its actual scalar action. -/
theorem harrisLatticeComparisonScalar_forward
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)
    (hx : x ∈ harrisLattice ρ p U) :
    harrisLatticeComparisonScalar ρ p U V • x ∈ harrisLattice ρ p V := by
  change harrisCoefficientIntegralEquiv L p W
    (harrisLatticeComparisonScalar ρ p U V • x) ∈ harrisProductLattice ρ p V
  rw [LinearEquiv.map_smul]
  exact harrisProductLatticeComparisonScalar_forward ρ p U V _ hx

theorem harrisLatticeComparisonScalar_backward
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)
    (hx : x ∈ harrisLattice ρ p V) :
    harrisLatticeComparisonScalar ρ p U V • x ∈ harrisLattice ρ p U := by
  change harrisCoefficientIntegralEquiv L p W
    (harrisLatticeComparisonScalar ρ p U V • x) ∈ harrisProductLattice ρ p U
  rw [LinearEquiv.map_smul]
  exact harrisProductLatticeComparisonScalar_backward ρ p U V _ hx

/-- An actual scalar linear map between independently constructed original lattices. -/
def harrisLatticeScaledComparison :
    harrisLattice ρ p U →ₗ[HarrisCoefficientIntegers L p] harrisLattice ρ p V :=
  ((DistribSMul.toLinearMap (HarrisCoefficientIntegers L p)
    ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)
    (harrisLatticeComparisonScalar ρ p U V)).comp (harrisLattice ρ p U).subtype).codRestrict
      (harrisLattice ρ p V)
      (fun x => harrisLatticeComparisonScalar_forward ρ p U V x x.2)

/-- The reverse scalar map uses exactly the same product scalar. -/
def harrisLatticeScaledComparisonBack :
    harrisLattice ρ p V →ₗ[HarrisCoefficientIntegers L p] harrisLattice ρ p U :=
  ((DistribSMul.toLinearMap (HarrisCoefficientIntegers L p)
    ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)
    (harrisLatticeComparisonScalar ρ p U V)).comp (harrisLattice ρ p V).subtype).codRestrict
      (harrisLattice ρ p U)
      (fun x => harrisLatticeComparisonScalar_backward ρ p U V x x.2)

@[simp] theorem harrisLatticeScaledComparison_coe (x : harrisLattice ρ p U) :
    (harrisLatticeScaledComparison ρ p U V x :
      (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) =
        harrisLatticeComparisonScalar ρ p U V • (x :
          (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) := rfl

@[simp] theorem harrisLatticeScaledComparisonBack_coe (x : harrisLattice ρ p V) :
    (harrisLatticeScaledComparisonBack ρ p U V x :
      (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) =
        harrisLatticeComparisonScalar ρ p U V • (x :
          (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) := rfl

/-- The forward map in the original tensor coordinates is multiplication by the unit in `B`. -/
theorem harrisLatticeScaledComparison_coe_tensor (x : harrisLattice ρ p U) :
    (harrisLatticeScaledComparison ρ p U V x :
      (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) =
        harrisCoefficientIntegersMap L p (harrisLatticeComparisonScalar ρ p U V) •
          (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :=
  harrisCoefficientIntegers_smul L p W _ _

theorem harrisLatticeScaledComparisonBack_coe_tensor (x : harrisLattice ρ p V) :
    (harrisLatticeScaledComparisonBack ρ p U V x :
      (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) =
        harrisCoefficientIntegersMap L p (harrisLatticeComparisonScalar ρ p U V) •
          (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :=
  harrisCoefficientIntegers_smul L p W _ _

/-- Splitting the original map gives exactly the constructed coordinatewise scalar maps. -/
theorem harrisLatticeScaledComparison_coordinate (x : harrisLattice ρ p U)
    (l : FinitePlacesAbove L p) :
    harrisCoefficientEquiv L p W (harrisLatticeScaledComparison ρ p U V x) l =
      latticeComparisonScalar
        (algebraicCompactCoefficientLattice ρ p l.1 U).carrier
        (algebraicCompactCoefficientLattice ρ p l.1 V).carrier •
          harrisCoefficientEquiv L p W x l := by
  exact congrFun ((harrisCoefficientIntegralEquiv L p W).map_smul
    (harrisLatticeComparisonScalar ρ p U V) (x :
      (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)) l

theorem harrisLatticeScaledComparison_back_comp :
    (harrisLatticeScaledComparisonBack ρ p U V).comp
        (harrisLatticeScaledComparison ρ p U V) =
      (harrisLatticeComparisonScalar ρ p U V * harrisLatticeComparisonScalar ρ p U V) •
        LinearMap.id := by
  ext x
  exact (mul_smul (harrisLatticeComparisonScalar ρ p U V)
    (harrisLatticeComparisonScalar ρ p U V)
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)).symm

theorem harrisLatticeScaledComparison_comp_back :
    (harrisLatticeScaledComparison ρ p U V).comp
        (harrisLatticeScaledComparisonBack ρ p U V) =
      (harrisLatticeComparisonScalar ρ p U V * harrisLatticeComparisonScalar ρ p U V) •
        LinearMap.id := by
  ext x
  exact (mul_smul (harrisLatticeComparisonScalar ρ p U V)
    (harrisLatticeComparisonScalar ρ p U V)
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)).symm

theorem harrisLatticeScaledComparison_injective :
    Function.Injective (harrisLatticeScaledComparison ρ p U V) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : harrisLattice ρ p V =>
    (z : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)) h
  rw [harrisLatticeScaledComparison_coe_tensor,
    harrisLatticeScaledComparison_coe_tensor] at h'
  exact (harrisLatticeComparisonScalar_isUnit ρ p U V).smul_left_cancel.mp h'

theorem harrisLatticeScaledComparisonBack_injective :
    Function.Injective (harrisLatticeScaledComparisonBack ρ p U V) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : harrisLattice ρ p U =>
    (z : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)) h
  rw [harrisLatticeScaledComparisonBack_coe_tensor,
    harrisLatticeScaledComparisonBack_coe_tensor] at h'
  exact (harrisLatticeComparisonScalar_isUnit ρ p U V).smul_left_cancel.mp h'

section Actions

variable (T : Subgroup σ.FiniteAdelicPoints)
  (hTU : T ≤ U.subgroup) (hTV : T ≤ V.subgroup)

/-- Both original representations restricted to any common subgroup are intertwined. -/
def harrisLatticeScaledComparisonAction :
    (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
      (Subgroup.inclusion hTU)).obj (harrisLatticeAction ρ p U) ⟶
    (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
      (Subgroup.inclusion hTV)).obj (harrisLatticeAction ρ p V) where
  hom := ModuleCat.ofHom (harrisLatticeScaledComparison ρ p U V)
  comm g := by
    apply ModuleCat.hom_ext
    ext x
    change harrisLattice ρ p U at x
    apply Subtype.ext
    exact (((ρ.harrisAdelic p (g : σ.FiniteAdelicPoints)).restrictScalars
      (HarrisCoefficientIntegers L p)).map_smul
        (harrisLatticeComparisonScalar ρ p U V) (x :
          (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)).symm

/-- The reverse scalar map intertwines the same restricted original representations. -/
def harrisLatticeScaledComparisonBackAction :
    (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
      (Subgroup.inclusion hTV)).obj (harrisLatticeAction ρ p V) ⟶
    (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
      (Subgroup.inclusion hTU)).obj (harrisLatticeAction ρ p U) where
  hom := ModuleCat.ofHom (harrisLatticeScaledComparisonBack ρ p U V)
  comm g := by
    apply ModuleCat.hom_ext
    ext x
    change harrisLattice ρ p V at x
    apply Subtype.ext
    exact (((ρ.harrisAdelic p (g : σ.FiniteAdelicPoints)).restrictScalars
      (HarrisCoefficientIntegers L p)).map_smul
        (harrisLatticeComparisonScalar ρ p U V) (x :
          (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)).symm

end Actions

section Nested

variable (hVU : V.subgroup ≤ U.subgroup)

/-- At nested levels the reverse comparison is the scalar multiple of the original inclusion. -/
theorem harrisLatticeScaledComparisonBack_eq_smul_inclusion :
    harrisLatticeScaledComparisonBack ρ p U V =
      harrisLatticeComparisonScalar ρ p U V • harrisLatticeInclusion ρ p U V hVU := by
  ext x
  rfl

/-- The comparison followed by the unchanged original inclusion is the scalar on `U`'s lattice. -/
theorem harrisLatticeInclusion_comp_scaledComparison :
    (harrisLatticeInclusion ρ p U V hVU).comp (harrisLatticeScaledComparison ρ p U V) =
      harrisLatticeComparisonScalar ρ p U V • LinearMap.id := by
  ext x
  rfl

/-- The other composite is the identical scalar on `V`'s lattice. -/
theorem harrisLatticeScaledComparison_comp_inclusion :
    (harrisLatticeScaledComparison ρ p U V).comp (harrisLatticeInclusion ρ p U V hVU) =
      harrisLatticeComparisonScalar ρ p U V • LinearMap.id := by
  ext x
  rfl

end Nested

end Langlands.Shimura.Coefficients
