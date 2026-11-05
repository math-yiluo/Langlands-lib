import Langlands.Global.NumberFieldSIntegerIntegralClosure
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.Global.IntegralClosureFractionTensor
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module

noncomputable section

universe u

open IsDedekindDomain
open scoped NumberField TensorProduct

namespace Langlands.Global

namespace NumberFieldSIntegers

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

scoped instance noetherian : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
  (adelicSIntegersNoetherian.2 K S).1

scoped instance dimensionLEOne : Ring.DimensionLEOne ((S : Set (FinitePlace K)).integer K) :=
  (adelicSIntegersNoetherian.2 K S).2

scoped instance integrallyClosed : IsIntegrallyClosed ((S : Set (FinitePlace K)).integer K) := by
  let R := (S : Set (FinitePlace K)).integer K
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ⟨⟨x, ?_⟩, rfl⟩
  intro p hp
  let V := (p.valuation K).valuationSubring
  let f : R →+* V := R.toSubring.subtype.codRestrict _ fun a => a.property p hp
  let : Algebra R V := f.toAlgebra
  let : IsScalarTower R V K := .of_algebraMap_eq fun _ => rfl
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff K).mp
    (inferInstance : IsIntegrallyClosed V) (hx.tower_top : IsIntegral V x)
  exact ha ▸ a.property

scoped instance dedekind : IsDedekindDomain ((S : Set (FinitePlace K)).integer K) := by
  let R := (S : Set (FinitePlace K)).integer K
  exact (isDedekindDomain_iff R K).mpr ⟨inferInstance, inferInstance, inferInstance,
    fun {_} => (isIntegrallyClosed_iff K).mp (inferInstance : IsIntegrallyClosed R)⟩

variable (L : Type u) [Field L] [NumberField L] [Algebra K L]

scoped instance isIntegralClosure : IsIntegralClosure
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)
    ((S : Set (FinitePlace K)).integer K) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    change x ∈ integralClosure ((S : Set (FinitePlace K)).integer K) L ↔ _
    change x ∈ (integralClosure ((S : Set (FinitePlace K)).integer K) L).toSubring ↔ _
    rw [numberFieldSIntegers_integralClosure_eq S]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

scoped instance finite : Module.Finite ((S : Set (FinitePlace K)).integer K)
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) :=
  IsIntegralClosure.finite ((S : Set (FinitePlace K)).integer K) K L _

scoped instance torsionFree : Module.IsTorsionFree ((S : Set (FinitePlace K)).integer K)
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) := by
  let R := (S : Set (FinitePlace K)).integer K
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  exact IsIntegralClosure.isTorsionFree R L

scoped instance projective : Module.Projective ((S : Set (FinitePlace K)).integer K)
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) := by
  let R := (S : Set (FinitePlace K)).integer K
  let B := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)
  let : Module.FinitePresentation R B := Module.finitePresentation_of_finite R B
  exact Module.Flat.projective_of_finitePresentation

end NumberFieldSIntegers

open scoped NumberFieldSIntegers

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

/-- Every prime localization of the original upper S-integer module is free. -/
theorem numberFieldSIntegers_local_free
    (p : Ideal ((S : Set (FinitePlace K)).integer K)) [p.IsPrime] :
    Module.Free (Localization.AtPrime p)
      (LocalizedModule p.primeCompl
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L)) :=
  Module.free_of_flat_of_isLocalRing

/-- The generic rank of the actual integer extension is the original field degree. -/
theorem numberFieldSIntegers_finrank_eq :
    Module.finrank ((S : Set (FinitePlace K)).integer K)
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq ((S : Set (FinitePlace K)).integer K) K
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) L).symm

/-- The generic-fiber algebra of the original full-preimage S-integer extension. -/
def numberFieldSIntegersFractionTensorEquiv :
    K ⊗[(S : Set (FinitePlace K)).integer K]
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) ≃ₐ[K] L :=
  integralClosureFractionTensorEquiv ((S : Set (FinitePlace K)).integer K) _ K L

@[simp]
theorem numberFieldSIntegersFractionTensorEquiv_tmul
    (a : K) (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) :
    numberFieldSIntegersFractionTensorEquiv K L S (a ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) =
      algebraMap K L a * (b : L) :=
  integralClosureFractionTensorEquiv_tmul ((S : Set (FinitePlace K)).integer K) _ K L a b

end Langlands.Global
