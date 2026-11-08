import Langlands.Shimura.Coefficients.HarrisLatticeCommensurability
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Whiskering

/-! # Scalar comparisons of the original Harris torsion systems -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite Langlands.Global AdelicFunctoriality AlgebraInvolution
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
  (m : ℕ) (T : Subgroup σ.FiniteAdelicPoints)

/-- Restrict the existing torsion system, retaining its quotients and exponent transitions. -/
abbrev harrisRestrictedTorsionSystem (hTU : T ≤ U.subgroup) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u} (HarrisCoefficientIntegers L p)) T :=
  harrisTorsionSystem ρ p U m ⋙
    Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p)) (Subgroup.inclusion hTU)

variable (hTU : T ≤ U.subgroup) (hTV : T ≤ V.subgroup)

/-- Reduce the original forward scalar map at every exponent on any common subgroup. -/
def harrisTorsionSystemScaledComparison :
    harrisRestrictedTorsionSystem ρ p U m T hTU ⟶
      harrisRestrictedTorsionSystem ρ p V m T hTV where
  app k := ((Langlands.Coefficients.AdicSystem.powerReduction
    (harrisCoefficientScalarIdeal L p m) k.unop).mapAction T).map
      (harrisLatticeScaledComparisonAction ρ p U V T hTU hTV)
  naturality {i j} f := by
    apply Action.Hom.ext
    exact ((Langlands.Coefficients.AdicSystem.transition
      (harrisCoefficientScalarIdeal L p m) (leOfHom f.unop)).naturality
        (harrisLatticeScaledComparisonAction ρ p U V T hTU hTV).hom).symm

/-- Reduce the original reverse scalar map using the same ordered-choice scalar. -/
def harrisTorsionSystemScaledComparisonBack :
    harrisRestrictedTorsionSystem ρ p V m T hTV ⟶
      harrisRestrictedTorsionSystem ρ p U m T hTU where
  app k := ((Langlands.Coefficients.AdicSystem.powerReduction
    (harrisCoefficientScalarIdeal L p m) k.unop).mapAction T).map
      (harrisLatticeScaledComparisonBackAction ρ p U V T hTU hTV)
  naturality {i j} f := by
    apply Action.Hom.ext
    exact ((Langlands.Coefficients.AdicSystem.transition
      (harrisCoefficientScalarIdeal L p m) (leOfHom f.unop)).naturality
        (harrisLatticeScaledComparisonBackAction ρ p U V T hTU hTV).hom).symm

@[simp] theorem harrisTorsionSystemScaledComparison_mk (k : ℕᵒᵖ)
    (x : harrisLattice ρ p U) :
    ((harrisTorsionSystemScaledComparison ρ p U V m T hTU hTV).app k).hom.hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeScaledComparison ρ p U V x) := rfl

@[simp] theorem harrisTorsionSystemScaledComparisonBack_mk (k : ℕᵒᵖ)
    (x : harrisLattice ρ p V) :
    ((harrisTorsionSystemScaledComparisonBack ρ p U V m T hTU hTV).app k).hom.hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeScaledComparisonBack ρ p U V x) := rfl

/-- The comparison commutes with all original exponent transitions. -/
@[reassoc] theorem harrisTorsionSystemScaledComparison_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisRestrictedTorsionSystem ρ p U m T hTU).map f ≫
        (harrisTorsionSystemScaledComparison ρ p U V m T hTU hTV).app j =
      (harrisTorsionSystemScaledComparison ρ p U V m T hTU hTV).app i ≫
        (harrisRestrictedTorsionSystem ρ p V m T hTV).map f :=
  (harrisTorsionSystemScaledComparison ρ p U V m T hTU hTV).naturality f

@[reassoc] theorem harrisTorsionSystemScaledComparisonBack_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisRestrictedTorsionSystem ρ p V m T hTV).map f ≫
        (harrisTorsionSystemScaledComparisonBack ρ p U V m T hTU hTV).app j =
      (harrisTorsionSystemScaledComparisonBack ρ p U V m T hTU hTV).app i ≫
        (harrisRestrictedTorsionSystem ρ p U m T hTU).map f :=
  (harrisTorsionSystemScaledComparisonBack ρ p U V m T hTU hTV).naturality f

/-- On the original system at `U`, the two maps compose to the square scalar. -/
theorem harrisTorsionSystemScaledComparison_back_comp :
    harrisTorsionSystemScaledComparison ρ p U V m T hTU hTV ≫
        harrisTorsionSystemScaledComparisonBack ρ p U V m T hTU hTV =
      (harrisLatticeComparisonScalar ρ p U V * harrisLatticeComparisonScalar ρ p U V) •
        𝟙 (harrisRestrictedTorsionSystem ρ p U m T hTU) := by
  apply NatTrans.ext
  funext k
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk
      (harrisLatticeScaledComparisonBack ρ p U V (harrisLatticeScaledComparison ρ p U V y)) =
    Submodule.Quotient.mk
      ((harrisLatticeComparisonScalar ρ p U V * harrisLatticeComparisonScalar ρ p U V) • y)
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (harrisLatticeScaledComparison_back_comp ρ p U V) y)

/-- On the original system at `V`, the opposite composite is the same square scalar. -/
theorem harrisTorsionSystemScaledComparison_comp_back :
    harrisTorsionSystemScaledComparisonBack ρ p U V m T hTU hTV ≫
        harrisTorsionSystemScaledComparison ρ p U V m T hTU hTV =
      (harrisLatticeComparisonScalar ρ p U V * harrisLatticeComparisonScalar ρ p U V) •
        𝟙 (harrisRestrictedTorsionSystem ρ p V m T hTV) := by
  apply NatTrans.ext
  funext k
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk
      (harrisLatticeScaledComparison ρ p U V (harrisLatticeScaledComparisonBack ρ p U V y)) =
    Submodule.Quotient.mk
      ((harrisLatticeComparisonScalar ρ p U V * harrisLatticeComparisonScalar ρ p U V) • y)
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (harrisLatticeScaledComparison_comp_back ρ p U V) y)

section Nested

variable (hVU : V.subgroup ≤ U.subgroup)

/-- Restrict the unchanged original torsion inclusion to a subgroup of the smaller level. -/
def harrisRestrictedTorsionSystemInclusion :
    harrisRestrictedTorsionSystem ρ p V m T hTV ⟶
      harrisRestrictedTorsionSystem ρ p U m T (hTV.trans hVU) :=
  Functor.whiskerRight (harrisTorsionSystemInclusion ρ p U V hVU m)
    (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p)) (Subgroup.inclusion hTV))

@[simp] theorem harrisRestrictedTorsionSystemInclusion_mk (k : ℕᵒᵖ)
    (x : harrisLattice ρ p V) :
    ((harrisRestrictedTorsionSystemInclusion ρ p U V m T hTV hVU).app k).hom.hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeInclusion ρ p U V hVU x) := rfl

/-- The reverse reduced comparison is a scalar multiple of the original inclusion. -/
theorem harrisTorsionSystemScaledComparisonBack_eq_smul_inclusion :
    harrisTorsionSystemScaledComparisonBack ρ p U V m T (hTV.trans hVU) hTV =
      harrisLatticeComparisonScalar ρ p U V •
        harrisRestrictedTorsionSystemInclusion ρ p U V m T hTV hVU := by
  apply NatTrans.ext
  funext k
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (harrisLatticeScaledComparisonBack ρ p U V y) =
    Submodule.Quotient.mk
      (harrisLatticeComparisonScalar ρ p U V • harrisLatticeInclusion ρ p U V hVU y)
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (harrisLatticeScaledComparisonBack_eq_smul_inclusion ρ p U V hVU) y)

/-- Factoring through the original inclusion gives the scalar on `U`'s torsion system. -/
theorem harrisRestrictedTorsionSystemInclusion_comp_scaledComparison :
    harrisTorsionSystemScaledComparison ρ p U V m T (hTV.trans hVU) hTV ≫
        harrisRestrictedTorsionSystemInclusion ρ p U V m T hTV hVU =
      harrisLatticeComparisonScalar ρ p U V •
        𝟙 (harrisRestrictedTorsionSystem ρ p U m T (hTV.trans hVU)) := by
  apply NatTrans.ext
  funext k
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk
      (harrisLatticeInclusion ρ p U V hVU (harrisLatticeScaledComparison ρ p U V y)) =
    Submodule.Quotient.mk (harrisLatticeComparisonScalar ρ p U V • y)
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (harrisLatticeInclusion_comp_scaledComparison ρ p U V hVU) y)

/-- The other factorization gives the identical scalar on `V`'s torsion system. -/
theorem harrisTorsionSystemScaledComparison_comp_restrictedInclusion :
    harrisRestrictedTorsionSystemInclusion ρ p U V m T hTV hVU ≫
        harrisTorsionSystemScaledComparison ρ p U V m T (hTV.trans hVU) hTV =
      harrisLatticeComparisonScalar ρ p U V •
        𝟙 (harrisRestrictedTorsionSystem ρ p V m T hTV) := by
  apply NatTrans.ext
  funext k
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk
      (harrisLatticeScaledComparison ρ p U V (harrisLatticeInclusion ρ p U V hVU y)) =
    Submodule.Quotient.mk (harrisLatticeComparisonScalar ρ p U V • y)
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (harrisLatticeScaledComparison_comp_inclusion ρ p U V hVU) y)

end Nested

end Langlands.Shimura.Coefficients
