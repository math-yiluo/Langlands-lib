import Langlands.Algebra.RenardAdditiveLocalizationNoetherianStatements
import Langlands.Algebra.RenardEndomorphismLocalizationKernelProof
import Langlands.LinearAlgebra.NoetherianLocalizationCoreProof

/-!
# Noetherian actual localization of additive nonunital actions: proof

Proof of the internal derived targets motivated by Renard 2026, C.II,
printed p. 279 / PDF p. 285. The helpers hold over any commutative scalar ring;
the targets use the canonical integer scalars. The actual intertwiners become
linear maps over the unitization, and the ordinary Noetherian localization core applies.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Renard.AdditiveActionLocalization

open Langlands.Algebra EndomorphismLocalization AlgebraActionLocalization
open Langlands.LinearAlgebra.NoetherianLocalizationCore

universe uk uA uV

section Unitized

variable {k : Type uk} [CommRing k] {A : Type uA} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {V : Type uV} [AddCommGroup V] [Module k V]

/-- The actual localized operator and its actual inverse, as an automorphism of the
localization over the unitization, for the selected localized action. -/
def unitizedLocalizationEquiv (a : Module.End k V) (ρ : A →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) :
    letI := CompatibleUnitization.module (localizedAction a ρ ha)
    Localized a ≃ₗ[Unitization k A] Localized a :=
  letI := CompatibleUnitization.module (localizedAction a ρ ha)
  LinearEquiv.ofLinearMap
    (CompatibleUnitization.ofLinearIntertwiner (localizedEndIntertwiner a ρ ha))
    (CompatibleUnitization.ofLinearIntertwiner (localizedInvIntertwiner a ρ ha))
    (LinearMap.ext (localizedEnd_localizedInv a))
    (LinearMap.ext (localizedInv_localizedEnd a))

/-- Powers of the unitized automorphism are the powers of the actual localized operator. -/
theorem unitizedLocalizationEquiv_pow_apply (a : Module.End k V)
    (ρ : A →ₙₐ[k] Module.End k V) (ha : ∀ b z, a (ρ b z) = ρ b (a z))
    (n : ℕ) (y : Localized a) :
    (letI := CompatibleUnitization.module (localizedAction a ρ ha);
      (unitizedLocalizationEquiv a ρ ha ^ n) y) = (localizedEnd a ^ n) y := by
  let _ := CompatibleUnitization.module (localizedAction a ρ ha)
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

/-- Powers of the unitized endomorphism of an actual self-intertwiner are the powers of
its underlying scalar-linear map. -/
theorem unitizedSelf_pow_apply (ρ : A →ₙₐ[k] Module.End k V) (g : LinearIntertwiner ρ ρ)
    (n : ℕ) (x : V) :
    (letI := CompatibleUnitization.module ρ;
      (CompatibleUnitization.ofLinearIntertwiner g ^ n) x) = (g.toLinearMap ^ n) x := by
  let _ := CompatibleUnitization.module ρ
  rw [Module.End.pow_apply, Module.End.pow_apply]
  rfl

/-- The certificates of the Noetherian localization core for the actual unitized maps:
the intertwining identity and inverse-power exhaustion. -/
theorem unitized_intertwines_exhausts (ρ : A →ₙₐ[k] Module.End k V)
    (g : LinearIntertwiner ρ ρ)
    (ha : ∀ b z, g.toLinearMap (ρ b z) = ρ b (g.toLinearMap z)) :
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
    (∀ x : V, CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner g.toLinearMap ρ ha)
        (CompatibleUnitization.ofLinearIntertwiner g x) =
      unitizedLocalizationEquiv g.toLinearMap ρ ha
        (CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner g.toLinearMap ρ ha) x)) ∧
    (∀ y : Localized g.toLinearMap, ∃ (n : ℕ) (x : V),
      (unitizedLocalizationEquiv g.toLinearMap ρ ha ^ n) y =
        CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner g.toLinearMap ρ ha) x) := by
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
  refine ⟨fun x => iota_intertwines g.toLinearMap x, fun y => ?_⟩
  obtain ⟨x, n, rfl⟩ := frac_surjective g.toLinearMap y
  exact ⟨n, x, (unitizedLocalizationEquiv_pow_apply g.toLinearMap ρ ha n _).trans
    (localizedEnd_pow_frac g.toLinearMap x n)⟩

/-- Noetherianity of the actual unitized localization alone gives surjectivity of the
actual canonical map. -/
theorem surjective_of_isNoetherian_unitized (ρ : A →ₙₐ[k] Module.End k V)
    (g : LinearIntertwiner ρ ρ)
    (ha : ∀ b z, g.toLinearMap (ρ b z) = ρ b (g.toLinearMap z)) :
    letI := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
    IsNoetherian (Unitization k A) (Localized g.toLinearMap) →
      Function.Surjective (iota g.toLinearMap) := by
  let _ := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
  let _ := CompatibleUnitization.module ρ
  intro hL
  obtain ⟨hg, hex⟩ := unitized_intertwines_exhausts ρ g ha
  exact exhaustion_surjective (CompatibleUnitization.ofLinearIntertwiner g)
    (unitizedLocalizationEquiv g.toLinearMap ρ ha)
    (CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner g.toLinearMap ρ ha)) hg hex

/-- Noetherianity of both actual unitized modules gives surjectivity of the actual
canonical map and one positive exponent for its kernel and both stability equalities,
for the scalar-linear powers of the underlying map. -/
theorem stabilization_of_isNoetherian_unitized (ρ : A →ₙₐ[k] Module.End k V)
    (g : LinearIntertwiner ρ ρ)
    (ha : ∀ b z, g.toLinearMap (ρ b z) = ρ b (g.toLinearMap z)) :
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
    IsNoetherian (Unitization k A) V →
      IsNoetherian (Unitization k A) (Localized g.toLinearMap) →
        Function.Surjective (iota g.toLinearMap) ∧
          ∃ n : ℕ, 0 < n ∧
            LinearMap.ker (iota g.toLinearMap) = LinearMap.ker (g.toLinearMap ^ n) ∧
            LinearMap.ker (g.toLinearMap ^ n) = LinearMap.ker ((g.toLinearMap ^ n) ^ 2) ∧
            LinearMap.range (g.toLinearMap ^ n) =
              LinearMap.range ((g.toLinearMap ^ n) ^ 2) := by
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
  intro hV hL
  obtain ⟨hg, hex⟩ := unitized_intertwines_exhausts ρ g ha
  have hnil : ∀ x : V,
      CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner g.toLinearMap ρ ha) x = 0 →
        ∃ n : ℕ, (CompatibleUnitization.ofLinearIntertwiner g ^ n) x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := (iota_eq_zero_iff g.toLinearMap x).mp hx
    exact ⟨n, (unitizedSelf_pow_apply ρ g n x).trans hn⟩
  obtain ⟨hsurj, n, hn, hker, hstabker, hstabrange⟩ :=
    localization_core (CompatibleUnitization.ofLinearIntertwiner g)
      (unitizedLocalizationEquiv g.toLinearMap ρ ha)
      (CompatibleUnitization.ofLinearIntertwiner (iotaIntertwiner g.toLinearMap ρ ha))
      hg hex hnil
  have hpow : ∀ x : V,
      (CompatibleUnitization.ofLinearIntertwiner g ^ n) x = (g.toLinearMap ^ n) x :=
    unitizedSelf_pow_apply ρ g n
  have hpow2 : ∀ x : V,
      ((CompatibleUnitization.ofLinearIntertwiner g ^ n) ^ 2) x =
        ((g.toLinearMap ^ n) ^ 2) x := by
    intro x
    rw [pow_two, pow_two, Module.End.mul_apply, Module.End.mul_apply, hpow, hpow]
  refine ⟨hsurj, n, hn, ?_, ?_, ?_⟩
  · ext x
    have h := SetLike.ext_iff.mp hker x
    rw [LinearMap.mem_ker, LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hpow]
    exact h
  · ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hpow, ← hpow2]
    simpa only [LinearMap.mem_ker] using SetLike.ext_iff.mp hstabker x
  · ext y
    simp only [LinearMap.mem_range, ← hpow, ← hpow2]
    simpa only [LinearMap.mem_range] using SetLike.ext_iff.mp hstabrange y

/-- Finite generation over the actual Noetherian unitization gives the same conclusion. -/
theorem stabilization_of_finite_unitized (ρ : A →ₙₐ[k] Module.End k V)
    (g : LinearIntertwiner ρ ρ)
    (ha : ∀ b z, g.toLinearMap (ρ b z) = ρ b (g.toLinearMap z)) :
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
    IsNoetherianRing (Unitization k A) →
      Module.Finite (Unitization k A) V →
      Module.Finite (Unitization k A) (Localized g.toLinearMap) →
        Function.Surjective (iota g.toLinearMap) ∧
          ∃ n : ℕ, 0 < n ∧
            LinearMap.ker (iota g.toLinearMap) = LinearMap.ker (g.toLinearMap ^ n) ∧
            LinearMap.ker (g.toLinearMap ^ n) = LinearMap.ker ((g.toLinearMap ^ n) ^ 2) ∧
            LinearMap.range (g.toLinearMap ^ n) =
              LinearMap.range ((g.toLinearMap ^ n) ^ 2) := by
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.module (localizedAction g.toLinearMap ρ ha)
  intro hR hV hL
  exact stabilization_of_isNoetherian_unitized ρ g ha
    (isNoetherian_of_isNoetherianRing_of_finite (Unitization k A) V)
    (isNoetherian_of_isNoetherianRing_of_finite (Unitization k A) (Localized g.toLinearMap))

end Unitized

/-- The closed internal actual-localization targets for original additive actions:
the helpers at the canonical integer scalars, for the canonical integer action and the
canonical integer intertwiner of the original map. -/
theorem additiveLocalizationNoetherian :
    AdditiveLocalizationNoetherianStatements.{uA, uV} :=
  ⟨fun _ _ _ _ _ f =>
      surjective_of_isNoetherian_unitized _ f.toIntLinearIntertwiner fun b v => f.map_smul b v,
    fun _ _ _ _ _ f =>
      stabilization_of_isNoetherian_unitized _ f.toIntLinearIntertwiner
        fun b v => f.map_smul b v,
    fun _ _ _ _ _ f =>
      stabilization_of_finite_unitized _ f.toIntLinearIntertwiner fun b v => f.map_smul b v⟩

end Langlands.Renard.AdditiveActionLocalization
