import Langlands.Galois.Local.SeparableUnramifiedIntegerRing
import Langlands.Geometry.FormalGroup.AdicCoefficientMap
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # The completed integer ring of the actual maximal unramified extension -/

noncomputable section

set_option maxHeartbeats 900000

universe u v w

open IsLocalRing ValuativeRel
open scoped NNReal

namespace Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance completedUnramifiedNormedField : NontriviallyNormedField F := localNormedField F

/-- The structural map of actual valuation rings. -/
instance fixedFieldIntegersAlgebra : Algebra 𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger (vR := ValuativeRel.valuation F)
    (vA := fixedFieldValuation F)

/-- The integer ring of the actual maximal unramified extension is a DVR. -/
instance fixedFieldIntegersDiscreteValuationRing :
    IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

/-- The completion of the valuation ring in the actual separable inertia fixed field. -/
abbrev CompletedUnramifiedIntegers := UnramifiedCompletion.Integers F

/-- The completed coefficient ring receives the actual uncompleted integers. -/
def toCompletedUnramifiedIntegers : fixedFieldIntegers F →ₐ[𝒪[F]] CompletedUnramifiedIntegers F :=
  IsScalarTower.toAlgHom 𝒪[F] (fixedFieldIntegers F) _

/-- Equality of value groups makes the upstairs maximal ideal the extension of the
base maximal ideal. -/
theorem fixedFieldMaximalIdeal_eq_map :
    maximalIdeal (fixedFieldIntegers F) =
      (maximalIdeal 𝒪[F]).map (integerToFixedField F) := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr ?_)
  · intro x hx
    have hxlt := (mem_maximalIdeal_iff_lt (fixedFieldValuation F) x).mp hx
    obtain ⟨a, ha⟩ := fixedFieldValuesFromBase F (x : inertiaFixedField F)
    have hv : fixedFieldValuation F (algebraMap F (inertiaFixedField F) a) =
        fixedFieldValuation F (x : inertiaFixedField F) :=
      (fixedFieldValuation_base F a).trans ha.symm
    have ha' : ValuativeRel.valuation F a ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (ValuativeRel.valuation F)
        (fixedFieldValuation F) a).mp (hv.le.trans x.2)
    let y : 𝒪[F] := ⟨a, ha'⟩
    have hy : y ∈ maximalIdeal 𝒪[F] := by
      rw [← maximalIdeal_comap (integerToFixedField F)]
      change integerToFixedField F y ∈ maximalIdeal (fixedFieldIntegers F)
      apply (mem_maximalIdeal_iff_lt (fixedFieldValuation F) _).mpr
      rw [coe_integerToFixedField, show (y : F) = a from rfl, hv]
      exact hxlt
    have hd : integerToFixedField F y ∣ x := by
      apply ((Valuation.integer.integers (fixedFieldValuation F)).dvd_iff_le).mpr
      change fixedFieldValuation F (x : inertiaFixedField F) ≤
        fixedFieldValuation F (algebraMap F (inertiaFixedField F) a)
      exact hv.ge
    obtain ⟨z, rfl⟩ := hd
    exact Ideal.mul_mem_right z _ (Ideal.mem_map_of_mem _ hy)
  · rw [maximalIdeal_comap]

/-- Any generator of the base maximal ideal still generates the maximal ideal of
the actual unramified integers. -/
theorem fixedFieldMaximalIdeal_eq_span (π : 𝒪[F]) (hπ : maximalIdeal 𝒪[F] = Ideal.span {π}) :
    maximalIdeal (fixedFieldIntegers F) = Ideal.span {algebraMap 𝒪[F] (fixedFieldIntegers F) π} := by
  rw [fixedFieldMaximalIdeal_eq_map, hπ, Ideal.map_span, Set.image_singleton]
  rfl

/-- Reduction of the completed integers has the actual unramified residue field. -/
def completedUnramifiedResidueEquiv :
    ResidueField (CompletedUnramifiedIntegers F) ≃+* ResidueField (fixedFieldIntegers F) :=
  (RingEquiv.ofBijective (ResidueField.map (algebraMap (fixedFieldIntegers F)
    (CompletedUnramifiedIntegers F))) (AdicCompletion.residueField_map_bijective _)).symm

@[simp]
theorem completedUnramifiedResidueEquiv_residue (x : fixedFieldIntegers F) :
    completedUnramifiedResidueEquiv F (residue _ (toCompletedUnramifiedIntegers F x)) = residue _ x := by
  have h : (completedUnramifiedResidueEquiv F).symm (residue _ x) =
      residue _ (toCompletedUnramifiedIntegers F x) :=
    ResidueField.map_residue (algebraMap (fixedFieldIntegers F) (CompletedUnramifiedIntegers F)) x
  rw [← h, RingEquiv.apply_symm_apply]

/-- The residue map on completed coefficients extends the actual map from the
base integers to the unramified residue field. -/
def completedUnramifiedReduction : CompletedUnramifiedIntegers F →ₐ[𝒪[F]]
    ResidueField (fixedFieldIntegers F) where
  __ := (completedUnramifiedResidueEquiv F).toRingHom.comp (residue _)
  commutes' a := completedUnramifiedResidueEquiv_residue F (integerToFixedField F a)

end Langlands.LocalGalois.Separable

namespace Langlands.FormalGroup.Nilp

open Langlands.LocalGalois.Separable

private theorem completionRestrict_bijective {O : Type u} [CommRing O] {π : O}
    {C : Type w} [CommRing C] [Algebra O C] {I : Ideal C}
    (hI : I = Ideal.span {algebraMap O C π}) (B : Nilp.{u, v} O π) :
    Function.Bijective (fun f : AdicCompletion I C →ₐ[O] B.obj =>
      f.comp (IsScalarTower.toAlgHom O C _)) := by
  subst I
  exact B.adicCoefficientMapEquiv.bijective

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {π : 𝒪[F]}

/-- Restriction from the completed unramified coefficient ring is a bijection
on every affine nilpotent test of the base uniformizer. -/
def completedUnramifiedMapEquiv (hπ : maximalIdeal 𝒪[F] = Ideal.span {π})
    (B : Nilp.{u, v} 𝒪[F] π) :
    (CompletedUnramifiedIntegers F →ₐ[𝒪[F]] B.obj) ≃
      (fixedFieldIntegers F →ₐ[𝒪[F]] B.obj) :=
  Equiv.ofBijective (fun f => f.comp (toCompletedUnramifiedIntegers F))
    (completionRestrict_bijective (fixedFieldMaximalIdeal_eq_span F π hπ) B)

end Langlands.FormalGroup.Nilp
