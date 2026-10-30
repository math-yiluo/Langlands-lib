import Langlands.Algebra.RenardAdditiveStableImageStatements
import Langlands.Algebra.RenardLocalizationStabilityProof

/-!
# Proof of the canonical stable image for additive nonunital actions

Internal finiteness-free refinement of Renard 2026, Appendix C.II,
printed p. 279 / PDF p. 285. The original additive data determine canonical
integer-linear actions and maps. The actual localization, local unitized powers
and compatible kernel/range are used unchanged.
-/

set_option autoImplicit false

namespace Langlands.Renard.AdditiveActionLocalization

open Langlands.Algebra Langlands.Renard.EndomorphismLocalization
open Langlands.Renard.AlgebraActionLocalization

universe uA uV

namespace AdditiveStableImageProof

/-- Select the existing generic localization module before specializing its coefficient ring. -/
private noncomputable abbrev localizedScalarModule
    {k : Type*} [CommRing k] {W : Type*} [AddCommGroup W] [Module k W]
    (a : Module.End k W) : Module k (Localized a) :=
  inferInstance

variable {A : Type uA} [NonUnitalRing A]
    {V : Type uV} [AddCommGroup V]

/-- Power coherence: the local unitized powers have the ordinary powers as underlying maps. -/
theorem powers_toLinearMap (ρ : A →ₙₐ[ℤ] Module.End ℤ V) (f : LinearIntertwiner ρ ρ)
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

/-- Complementarity transfers from integer submodules to the compatible lattice. -/
theorem isCompl_of_toSubmodule {ρ : A →ₙₐ[ℤ] Module.End ℤ V}
    {S T : CompatibleSubmodule ρ} (h : IsCompl S.toSubmodule T.toSubmodule) :
    IsCompl S T := by
  constructor
  · rw [disjoint_iff, ← CompatibleSubmodule.toSubmodule_inj,
      CompatibleSubmodule.inf_toSubmodule, CompatibleSubmodule.bot_toSubmodule]
    exact h.inf_eq_bot
  · rw [codisjoint_iff, ← CompatibleSubmodule.toSubmodule_inj,
      CompatibleSubmodule.sup_toSubmodule, CompatibleSubmodule.top_toSubmodule]
    exact h.sup_eq_top

/-- A positive stable power of an original additive intertwiner gives the canonical image. -/
theorem additiveStablePowerImageAt_of_stable [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V) (n : ℕ) (hn : 0 < n)
    (hk : LinearMap.ker (f.toAddMonoidHom.toIntLinearMap ^ n) =
      LinearMap.ker ((f.toAddMonoidHom.toIntLinearMap ^ n) ^ 2))
    (hr : LinearMap.range (f.toAddMonoidHom.toIntLinearMap ^ n) =
      LinearMap.range ((f.toAddMonoidHom.toIntLinearMap ^ n) ^ 2)) :
    AdditiveStablePowerImageAt f n := by
  unfold AdditiveStablePowerImageAt
  intro ρ a
  let _ := localizedScalarModule a
  intro σ powers K I
  have ha : ∀ b v, a (ρ b v) = ρ b (a v) := fun b v => f.map_smul b v
  have hpow : (powers n).toLinearMap = a ^ n :=
    powers_toLinearMap ρ f.toIntLinearIntertwiner n
  obtain ⟨hcompl, e0, ⟨-, he0⟩, -⟩ :=
    stablePowerImageStatement ℤ V a n hn hk hr
  have hI : I.toSubmodule = LinearMap.range (a ^ n) := by
    change LinearMap.range (powers n).toLinearMap = _
    exact congrArg LinearMap.range hpow
  have hK : K.toSubmodule = LinearMap.ker (a ^ n) := by
    change LinearMap.ker (powers n).toLinearMap = _
    exact congrArg LinearMap.ker hpow
  refine ⟨isCompl_of_toSubmodule (by rw [hK, hI]; exact hcompl), ?_⟩
  -- the canonical map restricted to `I`
  let g : I.toSubmodule →ₗ[ℤ] Localized a := (iota a).comp I.toSubmodule.subtype
  have hg0 : Function.Bijective ((iota a).comp (LinearMap.range (a ^ n)).subtype) := by
    rw [← he0]
    exact e0.symm.bijective
  have hg : Function.Bijective g := by
    change Function.Bijective (fun s : I.toSubmodule => iota a (s : V))
    exact hg0.comp (LinearEquiv.ofEq _ _ hI).bijective
  let e : Localized a ≃ₗ[ℤ] I.toSubmodule := (LinearEquiv.ofBijective g hg).symm
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

end AdditiveStableImageProof

/-- Every positive stable power of an original additive action gives its canonical stable image. -/
theorem additiveStablePowerImageStatement : AdditiveStablePowerImageStatement.{uA, uV} := by
  intro A _ V _ _ f n a hn hk hr
  exact AdditiveStableImageProof.additiveStablePowerImageAt_of_stable f n hn hk hr

end Langlands.Renard.AdditiveActionLocalization
