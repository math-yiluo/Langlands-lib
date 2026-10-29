import Langlands.Algebra.RenardCompatibleStableImageStatements
import Langlands.Algebra.RenardLocalizationStabilityProof

/-!
# Proof of the canonical compatible stable image

Internal finiteness-free refinement of Renard 2026, Appendix C.II,
printed p. 279 / PDF p. 285. The actual localization, compatible actions,
unitized powers and compatible kernel/range are used unchanged.
-/

set_option autoImplicit false

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra Langlands.Renard.EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

namespace CompatibleStableImageProof

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Power coherence: the local unitized powers have the ordinary powers as underlying maps. -/
theorem powers_toLinearMap (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ)
    (m : ℕ) :
    (letI := CompatibleUnitization.module ρ
     CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f) ^ m)).toLinearMap =
      f.toLinearMap ^ m := by
  let _ := CompatibleUnitization.module ρ
  induction m with
  | zero => rfl
  | succ m ih =>
    ext x
    have hx := LinearMap.congr_fun ih (f x)
    change (CompatibleUnitization.ofLinearIntertwiner f ^ (m + 1)) x =
      (f.toLinearMap ^ (m + 1)) x
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
    exact hx

omit [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] in
/-- Complementarity transfers from the underlying subspaces to the compatible lattice. -/
theorem isCompl_of_toSubmodule {ρ : B →ₙₐ[ℂ] Module.End ℂ V}
    {S T : CompatibleSubmodule ρ} (h : IsCompl S.toSubmodule T.toSubmodule) :
    IsCompl S T := by
  constructor
  · rw [disjoint_iff, ← CompatibleSubmodule.toSubmodule_inj,
      CompatibleSubmodule.inf_toSubmodule, CompatibleSubmodule.bot_toSubmodule]
    exact h.inf_eq_bot
  · rw [codisjoint_iff, ← CompatibleSubmodule.toSubmodule_inj,
      CompatibleSubmodule.sup_toSubmodule, CompatibleSubmodule.top_toSubmodule]
    exact h.sup_eq_top

/-- A positive stable power gives the canonical compatible stable image. -/
theorem compatibleStablePowerImageAt_of_stable (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (f : LinearIntertwiner ρ ρ) (n : ℕ) (hn : 0 < n) (hs : Stable (f.toLinearMap ^ n)) :
    CompatibleStablePowerImageAt ρ f n := by
  unfold CompatibleStablePowerImageAt
  intro a ha σ powers K I
  have hpow : (powers n).toLinearMap = a ^ n := powers_toLinearMap ρ f n
  obtain ⟨hcompl, e0, ⟨-, he0⟩, -⟩ :=
    stablePowerImageStatement ℂ V a n hn hs.1 hs.2
  have hI : I.toSubmodule = LinearMap.range (a ^ n) := by
    change LinearMap.range (powers n).toLinearMap = _
    exact congrArg LinearMap.range hpow
  have hK : K.toSubmodule = LinearMap.ker (a ^ n) := by
    change LinearMap.ker (powers n).toLinearMap = _
    exact congrArg LinearMap.ker hpow
  refine ⟨isCompl_of_toSubmodule (by rw [hK, hI]; exact hcompl), ?_⟩
  -- the canonical map restricted to `I`
  let g : I.toSubmodule →ₗ[ℂ] Localized a := (iota a).comp I.toSubmodule.subtype
  have hg0 : Function.Bijective ((iota a).comp (LinearMap.range (a ^ n)).subtype) := by
    rw [← he0]
    exact e0.symm.bijective
  have hgeq : g = ((iota a).comp (LinearMap.range (a ^ n)).subtype).comp
      (LinearEquiv.ofEq _ _ hI).toLinearMap := by
    ext s
    rfl
  have hg : Function.Bijective g := by
    rw [hgeq, LinearMap.coe_comp]
    exact hg0.comp (LinearEquiv.ofEq _ _ hI).bijective
  let e : Localized a ≃ₗ[ℂ] I.toSubmodule := (LinearEquiv.ofBijective g hg).symm
  have he_symm : ∀ s, e.symm s = iota a (s : V) := fun s => rfl
  have he : e.symm.toLinearMap = (iota a).comp I.toSubmodule.subtype :=
    LinearMap.ext fun s => he_symm s
  refine ⟨e, ⟨fun b z => ?_, LinearMap.ext fun z => ?_, he⟩, ?_⟩
  · -- action compatibility
    apply e.symm.injective
    rw [LinearEquiv.symm_apply_apply, he_symm, CompatibleSubmodule.restrictAction_apply_coe]
    change σ b z = iota a (ρ b (e z : V))
    rw [← localizedAction_iota a ρ ha b (e z : V), ← he_symm, LinearEquiv.symm_apply_apply]
  · -- operator compatibility
    have hstab : ∀ x : V, x ∈ I.toSubmodule → a x ∈ I.toSubmodule := by
      intro x hx
      rw [hI] at hx ⊢
      obtain ⟨y, rfl⟩ := hx
      refine ⟨a y, ?_⟩
      change (a ^ n * a) y = (a * a ^ n) y
      rw [← pow_succ, ← pow_succ']
    have hmem : a (e z : V) ∈ I.toSubmodule := hstab _ (e z).2
    have key : e (localizedEnd a z) = ⟨a (e z), hmem⟩ := by
      apply e.symm.injective
      rw [LinearEquiv.symm_apply_apply, he_symm]
      change localizedEnd a z = iota a (a (e z))
      rw [iota_intertwines, ← he_symm, LinearEquiv.symm_apply_apply]
    change ((e (localizedEnd a z) : I.toSubmodule) : V) = a (e z)
    rw [key]
  · -- uniqueness from the inverse equation alone
    rintro e' ⟨-, -, he'⟩
    exact LinearEquiv.symm_bijective.injective
      (LinearEquiv.toLinearMap_injective (he'.trans he.symm))

end CompatibleStableImageProof

/-- Every positive stable power identifies the actual localization canonically
with its compatible image, respecting the action and the operator. -/
theorem compatibleStablePowerImageStatement : CompatibleStablePowerImageStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f n hn hs
  exact CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable ρ f n hn hs

end Langlands.Renard.AlgebraActionLocalization
