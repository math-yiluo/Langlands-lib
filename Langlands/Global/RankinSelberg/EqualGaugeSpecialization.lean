import Langlands.Global.RankinSelberg.WhittakerSchwartzGaugeStatement
import Langlands.Global.RankinSelberg.EqualGaugeReduction
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization

/-! # The analytic gauge estimate on actual cusp functions

The general Whittaker–Schwartz estimate specializes to every actual cuspidal
realization, using its published decay class and uniform central exponent. -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance equalGaugeSpecializationAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalGaugeSpecializationSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The general analytic gauge estimate implies the Whittaker–Schwartz bound
for every actual cuspidal realization. -/
def EqualGaugeSpecializationStatement : Prop :=
  WhittakerSchwartzGaugeStatement.{u} → EqualWhittakerSchwartzStatement.{u}

namespace EqualGaugeSpecialization

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)

/-- The published central bound applies to the whole cusp-function space. -/
theorem hasCentralPowerBound_cuspSpace :
    HasCentralPowerBound F r (cuspSpace F T) := by
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_cuspFunction_le F T
  refine ⟨β, fun f => ?_⟩
  obtain ⟨B, hB0, hB⟩ := hβ ((cuspEquiv F T).symm f)
  refine ⟨B, hB0, fun g => ?_⟩
  rw [coe_eq_cuspFunction]
  exact hB g

/-- The class-space bound gives the corresponding realized-vector bound. -/
theorem equalWhittakerSchwartzBound_of_cuspSpace
    (hW : WhittakerSchwartzBound F r (cuspSpace F T)) :
    EqualWhittakerSchwartzBound F T := by
  obtain ⟨C, hC0, hW⟩ := hW
  refine ⟨C, hC0, fun ψ hψ v Φ hΦ σ hσ => ?_⟩
  exact hW ψ hψ (cuspEquiv F T v) Φ hΦ σ hσ

end EqualGaugeSpecialization

/-- Proof of the conditional specialization, with the same field universe. -/
theorem equalGaugeSpecialization : EqualGaugeSpecializationStatement.{u} := by
  intro h F _ _ _ r T
  exact EqualGaugeSpecialization.equalWhittakerSchwartzBound_of_cuspSpace F T
    (h F r (cuspSpace F T) (cuspDerivative F T)
      (whittakerDecayClass_cuspSpace F T)
      (EqualGaugeSpecialization.hasCentralPowerBound_cuspSpace F T))

end Langlands.Global.RankinSelbergGlobal
