import Langlands.Algebra.RenardCompatibleLocalizationNoetherianStatements
import Langlands.Algebra.RenardEndomorphismLocalizationKernelProof
import Langlands.LinearAlgebra.NoetherianLocalizationCoreProof

/-!
# Noetherian unitized actions on actual endomorphism localization: proof

Proof of the internal derived targets motivated by Renard 2026, C.II,
printed p. 279 / PDF p. 285. The actual intertwiners become linear maps
over the unitization, and the ordinary Noetherian localization core applies.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism
open Langlands.LinearAlgebra.NoetherianLocalizationCore

universe uB uV

section Unitized

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual localized operator and its actual inverse, as an automorphism of the
localization over the unitization, for the selected localized action. -/
def unitizedLocalizedEquiv (a : Module.End ℂ V) (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    letI := CompatibleUnitization.module (localizedAction a ρ ha)
    Localized a ≃ₗ[Unitization ℂ B] Localized a :=
  letI := CompatibleUnitization.module (localizedAction a ρ ha)
  LinearEquiv.ofLinearMap
    (CompatibleUnitization.ofLinearIntertwiner (localizedEndIntertwiner a ρ ha))
    (CompatibleUnitization.ofLinearIntertwiner (localizedInvIntertwiner a ρ ha))
    (LinearMap.ext (localizedEnd_localizedInv a))
    (LinearMap.ext (localizedInv_localizedEnd a))

/-- Powers of the unitized automorphism are the powers of the actual localized operator. -/
theorem unitizedLocalizedEquiv_pow_apply (a : Module.End ℂ V)
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (n : ℕ) (y : Localized a) :
    (letI := CompatibleUnitization.module (localizedAction a ρ ha);
      (unitizedLocalizedEquiv a ρ ha ^ n) y) = (localizedEnd a ^ n) y := by
  let _ := CompatibleUnitization.module (localizedAction a ρ ha)
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

/-- Powers of the unitized endomorphism of an actual self-intertwiner are the powers of
its underlying complex-linear map. -/
theorem unitized_pow_apply (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ)
    (n : ℕ) (x : V) :
    (letI := CompatibleUnitization.module ρ;
      (CompatibleUnitization.ofLinearIntertwiner f ^ n) x) = (f.toLinearMap ^ n) x := by
  let _ := CompatibleUnitization.module ρ
  rw [Module.End.pow_apply, Module.End.pow_apply]
  rfl

/-- The certificates of the Noetherian localization core for the actual unitized maps:
the intertwining identity and inverse-power exhaustion. -/
theorem unitized_intertwines_exhausts (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (f : LinearIntertwiner ρ ρ)
    (ha : ∀ b z, f.toLinearMap (ρ b z) = ρ b (f.toLinearMap z)) :
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module (localizedAction f.toLinearMap ρ ha)
    (∀ x : V, CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner f.toLinearMap ρ ha)
        (CompatibleUnitization.ofLinearIntertwiner f x) =
      unitizedLocalizedEquiv f.toLinearMap ρ ha
        (CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner f.toLinearMap ρ ha) x)) ∧
    (∀ y : Localized f.toLinearMap, ∃ (n : ℕ) (x : V),
      (unitizedLocalizedEquiv f.toLinearMap ρ ha ^ n) y =
        CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner f.toLinearMap ρ ha) x) := by
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.module (localizedAction f.toLinearMap ρ ha)
  refine ⟨fun x => iota_intertwines f.toLinearMap x, fun y => ?_⟩
  obtain ⟨x, n, rfl⟩ := frac_surjective f.toLinearMap y
  exact ⟨n, x, (unitizedLocalizedEquiv_pow_apply f.toLinearMap ρ ha n _).trans
    (localizedEnd_pow_frac f.toLinearMap x n)⟩

/-- Noetherianity of the actual unitized localization alone gives surjectivity of the
actual canonical map. -/
theorem surjective_of_isNoetherian (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (f : LinearIntertwiner ρ ρ)
    (ha : ∀ b z, f.toLinearMap (ρ b z) = ρ b (f.toLinearMap z)) :
    letI := CompatibleUnitization.module (localizedAction f.toLinearMap ρ ha)
    IsNoetherian (Unitization ℂ B) (Localized f.toLinearMap) →
      Function.Surjective (iota f.toLinearMap) := by
  let _ := CompatibleUnitization.module (localizedAction f.toLinearMap ρ ha)
  let _ := CompatibleUnitization.module ρ
  intro hL
  obtain ⟨hf, hex⟩ := unitized_intertwines_exhausts ρ f ha
  exact exhaustion_surjective (CompatibleUnitization.ofLinearIntertwiner f)
    (unitizedLocalizedEquiv f.toLinearMap ρ ha)
    (CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner f.toLinearMap ρ ha)) hf hex

/-- Noetherianity of both actual unitized modules gives the common positive exponent. -/
theorem stabilizationAt_of_isNoetherian (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (f : LinearIntertwiner ρ ρ) :
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module
      (localizedAction f.toLinearMap ρ fun b z => f.map_action' b z)
    IsNoetherian (Unitization ℂ B) V →
      IsNoetherian (Unitization ℂ B) (Localized f.toLinearMap) →
        CompatibleLocalizationStabilizationAt ρ f := by
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.module
    (localizedAction f.toLinearMap ρ fun b z => f.map_action' b z)
  intro hV hL
  obtain ⟨hf, hex⟩ := unitized_intertwines_exhausts ρ f fun b z => f.map_action' b z
  have hnil : ∀ x : V,
      CompatibleUnitization.ofLinearIntertwiner
        (iotaIntertwiner f.toLinearMap ρ fun b z => f.map_action' b z) x = 0 →
        ∃ n : ℕ, (CompatibleUnitization.ofLinearIntertwiner f ^ n) x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := (iota_eq_zero_iff f.toLinearMap x).mp hx
    exact ⟨n, (unitized_pow_apply ρ f n x).trans hn⟩
  obtain ⟨hsurj, n, hn, hker, hstabker, hstabrange⟩ :=
    localization_core (CompatibleUnitization.ofLinearIntertwiner f)
      (unitizedLocalizedEquiv f.toLinearMap ρ fun b z => f.map_action' b z)
      (CompatibleUnitization.ofLinearIntertwiner
        (iotaIntertwiner f.toLinearMap ρ fun b z => f.map_action' b z)) hf hex hnil
  have hpow : ∀ x : V,
      (CompatibleUnitization.ofLinearIntertwiner f ^ n) x = (f.toLinearMap ^ n) x :=
    unitized_pow_apply ρ f n
  have hpow2 : ∀ x : V,
      ((CompatibleUnitization.ofLinearIntertwiner f ^ n) ^ 2) x =
        ((f.toLinearMap ^ n) ^ 2) x := by
    intro x
    rw [pow_two, pow_two, Module.End.mul_apply, Module.End.mul_apply, hpow, hpow]
  dsimp only [CompatibleLocalizationStabilizationAt]
  refine ⟨hsurj, n, hn, ?_, ?_, ?_⟩
  · refine CompatibleSubmodule.ext fun x => ?_
    have h := SetLike.ext_iff.mp hker x
    rw [LinearMap.mem_ker, LinearMap.mem_ker] at h
    rw [LinearIntertwiner.mem_ker, LinearIntertwiner.mem_ker]
    exact h
  · ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hpow, ← hpow2]
    simpa only [LinearMap.mem_ker] using SetLike.ext_iff.mp hstabker x
  · ext y
    simp only [LinearMap.mem_range, ← hpow, ← hpow2]
    simpa only [LinearMap.mem_range] using SetLike.ext_iff.mp hstabrange y

/-- Finite generation over the actual Noetherian unitization gives the same conclusion. -/
theorem stabilizationAt_of_finite (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (f : LinearIntertwiner ρ ρ) :
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module
      (localizedAction f.toLinearMap ρ fun b z => f.map_action' b z)
    IsNoetherianRing (Unitization ℂ B) →
      Module.Finite (Unitization ℂ B) V →
      Module.Finite (Unitization ℂ B) (Localized f.toLinearMap) →
        CompatibleLocalizationStabilizationAt ρ f := by
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.module
    (localizedAction f.toLinearMap ρ fun b z => f.map_action' b z)
  intro hR hV hL
  exact stabilizationAt_of_isNoetherian ρ f
    (isNoetherian_of_isNoetherianRing_of_finite (Unitization ℂ B) V)
    (isNoetherian_of_isNoetherianRing_of_finite (Unitization ℂ B) (Localized f.toLinearMap))

end Unitized

/-- The closed internal actual-localization Noetherian adapter targets. -/
theorem compatibleLocalizationNoetherian :
    CompatibleLocalizationNoetherianStatements.{uB, uV} :=
  ⟨fun _ _ _ _ _ _ _ _ ρ f => surjective_of_isNoetherian ρ f _,
    fun _ _ _ _ _ _ _ _ ρ f => stabilizationAt_of_isNoetherian ρ f,
    fun _ _ _ _ _ _ _ _ ρ f => stabilizationAt_of_finite ρ f⟩

end Langlands.Renard.AlgebraActionLocalization
