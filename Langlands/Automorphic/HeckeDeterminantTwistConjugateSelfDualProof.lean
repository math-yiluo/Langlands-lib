import Langlands.Automorphic.HeckeDeterminantTwistDualitySupercuspidalStatement
import Langlands.Automorphic.RankOneHeckeConjugateSelfDual

/-! # Conjugate self-duality of an actual Hecke determinant twist -/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Global.CMConjugation
open Langlands.Global.AdelicFunctoriality (ideleClassComplexConj)
open NumberField (IsCMField)
open OperatorRealization

section Pairing

variable {V W : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]

/-- Pullback preserves group invariance when the two scalar factors multiply to one. -/
private theorem pairing_pullback_of_mul_eq_one (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (e : V ≃ₗ[ℂ] W)
    (ρc ρ : V →ₗ[ℂ] V) (σc σ : W →ₗ[ℂ] W) {a b : ℂ} (hab : a * b = 1)
    (hc : ∀ v, σc (e v) = a • e (ρc v)) (h : ∀ v, σ (e v) = b • e (ρ v))
    (hB : ∀ y x, B (ρc y) (ρ x) = B y x) (y x : W) :
    B (e.symm (σc y)) (e.symm (σ x)) = B (e.symm y) (e.symm x) := by
  rw [twist_symm_apply e ρc σc a hc, twist_symm_apply e ρ σ b h,
    LinearMap.map_smul₂, LinearMap.map_smul, smul_smul, hab, one_smul, hB]

/-- Pullback preserves Lie invariance when the two scalar shifts add to zero. -/
private theorem pairing_pullback_lie_of_add_eq_zero (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (e : V ≃ₗ[ℂ] W)
    (ρc ρ : V →ₗ[ℂ] V) (σc σ : W →ₗ[ℂ] W) {a b : ℂ} (hab : a + b = 0)
    (hc : ∀ v, σc (e v) = e (ρc v + a • v)) (h : ∀ v, σ (e v) = e (ρ v + b • v))
    (hB : ∀ y x, B (ρc y) x + B y (ρ x) = 0) (y x : W) :
    B (e.symm (σc y)) (e.symm x) + B (e.symm y) (e.symm (σ x)) = 0 := by
  obtain ⟨y, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [hc, h]
  simp only [LinearEquiv.symm_apply_apply, LinearMap.map_add, LinearMap.map_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [add_add_add_comm, ← add_smul, hab, zero_smul, hB, add_zero]

end Pairing

variable {E : Type u} [Field E] [NumberField E] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions E n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions E n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions E n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms E n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions E n) := Submodule.addCommGroup _
local instance (S : OperatorRealization E n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- On real Lie generators the enveloping shift adds the actual character derivative. -/
private theorem heckeEnvelopingShift_realGenerator (ν : HeckeCharacter E)
    (X : RealLieAlgebra E n) :
    heckeEnvelopingShift n ν (envelopingGenerator E n (complexify E n X)) =
      envelopingGenerator E n (complexify E n X) +
        algebraMap ℂ (EnvelopingAlgebra E n) (characterDifferential
          (ν.infiniteDeterminantCharacter n) (ν.infiniteDeterminantCharacter_mem_smoothFunctions n) X) := by
  rw [heckeEnvelopingShift, characterShift, envelopingShift_generator, complexify_apply,
    complexCharacterDifferential_tmul, one_mul]

/-- The inverse of actual determinant multiplication pulls back the conjugate
contragredient pairing in both arguments. -/
theorem heckeDeterminantTwistConjugateSelfDual :
    HeckeDeterminantTwistConjugateSelfDualStatement.{u} := by
  intro E _ _ _ n S ν hν hS
  have hpt (z : IdeleClasses E) : ν (ideleClassComplexConj z) = (ν z)⁻¹ :=
    congrArg (fun χ : HeckeCharacter E => χ z) hν
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := hS
  let T := S.heckeDeterminantTwist ν
  let e : S.Space ≃ₗ[ℂ] T.Space := (S.heckeDeterminantTwistEquiv ν).toLinearEquiv
  let B' := B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  refine ⟨B', ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    have hscalar : (ν.adelicDeterminant n (AdelicGL.ofFinite E n (finiteConj E n d)) : ℂ) *
        (ν.adelicDeterminant n (AdelicGL.ofFinite E n d) : ℂ) = 1 := by
      rw [← Units.val_mul, RankOneHecke.adelicDeterminant_ofFinite_finiteConj hpt,
        inv_mul_cancel, Units.val_one]
    exact pairing_pullback_of_mul_eq_one B e
      (S.finiteRepresentation (finiteConj E n d)) (S.finiteRepresentation d)
      (T.finiteRepresentation (finiteConj E n d)) (T.finiteRepresentation d) hscalar
      (S.heckeDeterminantTwistEquiv_finite ν (finiteConj E n d))
      (S.heckeDeterminantTwistEquiv_finite ν d) (hd d) y x
  · intro k y x
    have hscalar : (ν.adelicDeterminant n (AdelicGL.ofInfinite E n (compactConj E n k).val) : ℂ) *
        (ν.adelicDeterminant n (AdelicGL.ofInfinite E n k.val) : ℂ) = 1 := by
      rw [compactConj_val, ← Units.val_mul,
        RankOneHecke.adelicDeterminant_ofInfinite_infiniteConj hpt, inv_mul_cancel, Units.val_one]
    exact pairing_pullback_of_mul_eq_one B e
      (S.compactRepresentation (compactConj E n k)) (S.compactRepresentation k)
      (T.compactRepresentation (compactConj E n k)) (T.compactRepresentation k) hscalar
      (S.heckeDeterminantTwistEquiv_compact ν (compactConj E n k))
      (S.heckeDeterminantTwistEquiv_compact ν k) (hk k) y x
  · intro X y x
    exact pairing_pullback_lie_of_add_eq_zero B e
      (S.lieAction (lieConj E n X)) (S.lieAction X)
      (T.lieAction (lieConj E n X)) (T.lieAction X)
      (RankOneHecke.characterDifferential_lieConj hpt X)
      (S.lieAction_heckeDeterminantTwistEquiv ν (lieConj E n X)
        (heckeEnvelopingShift_realGenerator ν (lieConj E n X)))
      (S.lieAction_heckeDeterminantTwistEquiv ν X (heckeEnvelopingShift_realGenerator ν X)) (hX X) y x
  · intro x
    change T.IsContragredientFunctional ((B.flip (e.symm x)).comp e.symm.toLinearMap)
    exact isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm ν (hB (e.symm x))
  · exact pairing_flip_injective B e.symm e hinj
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj _ (isContragredientFunctional_comp_heckeDeterminantTwistEquiv ν hl)
    exact ⟨e x, pairing_flip_surjective B e.symm e l x hx⟩

end Langlands.Automorphic
