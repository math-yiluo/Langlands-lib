import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Mathlib.FieldTheory.Perfect

/-! # The induced residue algebra of the maximal unramified extension -/

noncomputable section
universe u

open scoped ValuativeRel
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance unramifiedResidueIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedResidueIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedResidueIntegerLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The residue-field algebra induced by the integral extension `𝒪[F] → O` is the
published residue map. -/
theorem unramifiedResidueAlgebra_eq :
    (inferInstance : Algebra (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) = (residueToFixedField F).toAlgebra := by
  apply Algebra.algebra_ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

/-- The residue field of `O` is algebraic over the residue field of `𝒪[F]`. -/
theorem unramifiedResidue_isAlgebraic :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have h := (fixedFieldResidueIsAlgClosure F).isAlgebraic
  convert h
  exact unramifiedResidueAlgebra_eq

/-- The residue field of `O` is separable over the finite residue field of `𝒪[F]`. -/
theorem unramifiedResidue_isSeparable :
    Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have : Finite (IsLocalRing.ResidueField ↥𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  have := unramifiedResidue_isAlgebraic (F := F)
  infer_instance

/-- The induced residue extension of the actual integer rings is separable algebraic. -/
def UnramifiedResidueArithmeticStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    Algebra.IsAlgebraic (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) ∧
    Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F))

/-- The induced residue arithmetic follows from its identification with the published residue map. -/
theorem unramifiedResidueArithmetic : UnramifiedResidueArithmeticStatement.{u} := by
  intro F _ _ _ _
  exact ⟨unramifiedResidue_isAlgebraic, unramifiedResidue_isSeparable⟩

end Langlands.BruhatTits.IntegralModels
