import Langlands.Correspondence.HenniartLadicUnramifiedCharacters
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.IrreducibleCharacter
import Langlands.Weil.Representation.RankDeterminantProof
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Topology.Instances.Matrix

/-! # Weil transport of ℓ-adic classes and unramified twists -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe uK uΩ uW

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation
open Weil.Local.SepClosed

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ →+* ℂ)

local notation "E" => PadicAlgCl ℓ
local notation "Γ" => Ω ≃ₐ[K] Ω
local notation "W" => localWeilGroup K Ω
local notation "π" => localProjection K Ω
local notation "πₘ" => ContinuousMonoidHom.toMonoidHom (localProjection K Ω)

omit [IsSepClosed Ω] in
private theorem exists_ladicRepresentative {k : ℕ}
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    ∃ A : FiniteRepresentation.{0, uΩ, uW} E Γ,
      IsLadicContinuous ℓ A ∧ Representation.IsIrreducible A.representation ∧
        classOf A = ladicClassForget K Ω ℓ ρ ∧ A.rank = k + 1 := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep ρ.val
  have hclass : classOf A.val = ladicClassForget K Ω ℓ ρ := by
    change forgetPropertyClass _ (Quotient.mk _ A) = forgetPropertyClass _ ρ.val
    rw [hA]
  exact ⟨A.val, A.property.1, A.property.2.2, hclass,
    (congrArg classRank hclass).trans ρ.property⟩

private def ladicDeterminant (A : FiniteRepresentation.{0, uΩ, uW} E Γ)
    (hA : IsLadicContinuous ℓ A) : Γ →ₜ* Eˣ where
  toMonoidHom := determinantCharacter A
  continuous_toFun := by
    let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
    let b := Module.finBasis E A
    have hc : Continuous (fun g => LinearMap.toMatrix b b (A.representation g)) :=
      (IsModuleTopology.continuous_of_linearMap (LinearMap.toMatrix b b).toLinearMap).comp hA
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    change Continuous fun g : Γ => LinearMap.det (A.representation g)
    simpa only [LinearMap.det_toMatrix] using hc.matrix_det

/-- The complex scalar of the restricted twist, evaluated at geometric
Frobenius through the specified coefficient embedding. -/
def ladicWeilTwistParameter : ladicUnramifiedCharacters K Ω ℓ →* ℂˣ :=
  (Units.map ι.toMonoidHom).comp
    ((ladicUnitSphere ℓ).subtype.comp (ladicUnramifiedCharacterEquiv ℓ K Ω).toMonoidHom)

theorem ladicWeilTwistParameter_injective :
    Function.Injective (ladicWeilTwistParameter K Ω ℓ ι) := by
  intro χ ψ h
  apply (ladicUnramifiedCharacterEquiv ℓ K Ω).injective
  apply Subtype.ext
  apply Units.ext
  exact ι.injective (congrArg Units.val h)

/-- Restriction followed by scalar extension commutes with unramified twisting. -/
theorem ladicWeilTransport_unramifiedTwist {k : ℕ}
    (χ : ladicUnramifiedCharacters K Ω ℓ)
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ (ladicUnramifiedTwist K Ω ℓ k χ ρ)) =
      twistClass (localUnramifiedCharacter K Ω (ladicWeilTwistParameter K Ω ℓ ι χ)).toMonoidHom
        (ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ)) := by
  rw [ladicClassForget_unramifiedTwist, twistClassEquiv_apply]
  let := ι.toAlgebra
  induction ladicClassForget K Ω ℓ ρ using Quotient.inductionOn with
  | h A =>
    change classOf (ladicScalarExtension ℓ ι
      (restrict πₘ (FiniteRepresentation.twist χ.val.toMonoidHom A))) =
      classOf (FiniteRepresentation.twist
        (localUnramifiedCharacter K Ω (ladicWeilTwistParameter K Ω ℓ ι χ)).toMonoidHom
        (ladicScalarExtension ℓ ι (restrict πₘ A)))
    refine (classOf_eq_iff _ _).mpr ⟨Representation.Equiv.mk
      (LinearEquiv.refl ℂ (ℂ ⊗[E] A)) fun w => ?_⟩
    have hχ : localUnramifiedCharacter K Ω (ladicWeilTwistParameter K Ω ℓ ι χ) w =
        Units.map ι.toMonoidHom (χ.val (π w)) := by
      rw [ladicUnramifiedCharacter_value_on_Weil ℓ K Ω, map_zpow]
      rfl
    change ((χ.val (π w) : E) • A.representation (π w)).baseChange ℂ =
      ((localUnramifiedCharacter K Ω (ladicWeilTwistParameter K Ω ℓ ι χ) w : ℂˣ) : ℂ) •
        (A.representation (π w)).baseChange ℂ
    rw [hχ, LinearMap.baseChange_smul]
    exact (IsScalarTower.algebraMap_smul ℂ (χ.val (π w) : E) _).symm

/-- The transported class determines the continuous irreducible ℓ-adic
Galois class. Character traces agree on the dense Weil projection. -/
theorem ladicWeilTransport_injective (k : ℕ) : Function.Injective
    (fun ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat =>
      ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ)) := by
  intro ρ σ h
  change ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ) =
    ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ σ) at h
  obtain ⟨A, hAc, hAi, hA, hrA⟩ := exists_ladicRepresentative K Ω ℓ ρ
  obtain ⟨B, hBc, _, hB, hrB⟩ := exists_ladicRepresentative K Ω ℓ σ
  rw [← hA, ← hB] at h
  change classOf (ladicScalarExtension ℓ ι (restrict πₘ A)) =
    classOf (ladicScalarExtension ℓ ι (restrict πₘ B)) at h
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp h
  let := ι.toAlgebra
  let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  let : TopologicalSpace (Module.End E B) := moduleTopology E (Module.End E B)
  have hAc' : Continuous A.representation.character :=
    (IsModuleTopology.continuous_of_linearMap (LinearMap.trace E A)).comp hAc
  have hBc' : Continuous B.representation.character :=
    (IsModuleTopology.continuous_of_linearMap (LinearMap.trace E B)).comp hBc
  have hchar : A.representation.character = B.representation.character := by
    apply (localProjection_denseRange K Ω).equalizer hAc' hBc'
    funext w
    have ht := congrFun (Representation.char_iso e) w
    change LinearMap.trace ℂ _ ((A.representation (π w)).baseChange ℂ) =
      LinearMap.trace ℂ _ ((B.representation (π w)).baseChange ℂ) at ht
    rw [LinearMap.trace_baseChange, LinearMap.trace_baseChange] at ht
    exact ι.injective ht
  apply Subtype.ext
  apply forgetPropertyClass_injective
  change ladicClassForget K Ω ℓ ρ = ladicClassForget K Ω ℓ σ
  rw [← hA, ← hB]
  exact (classOf_eq_iff _ _).mpr
    (irreducibleCharacterComparison A B hAi (hrA.trans hrB.symm) hchar)

private theorem exists_ladicUnit_of_power {d : ℕ} (hd : 0 < d) {a : Eˣ} {z : ℂˣ}
    (ha : ‖(a : E)‖ = 1) (hz : (z : ℂ) ^ d = ι (a : E)) :
    ∃ b : ladicUnitSphere ℓ, Units.map ι.toMonoidHom b.val = z := by
  let := ι.toAlgebra
  have hzPow : IsIntegral E ((z : ℂ) ^ d) := by
    rw [hz, ← RingHom.algebraMap_toAlgebra ι]
    exact isIntegral_algebraMap
  let L := IntermediateField.adjoin E ({(z : ℂ)} : Set ℂ)
  let : Algebra.IsAlgebraic E L := IntermediateField.isAlgebraic_adjoin_simple (hzPow.of_pow hd)
  have hL : L = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic L
  have hzL : (z : ℂ) ∈ L := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp (hL ▸ hzL)
  change ι b = (z : ℂ) at hb
  have hb0 : b ≠ 0 := fun h => z.ne_zero (by rw [← hb, h, map_zero])
  have hbPow : b ^ d = (a : E) := ι.injective (by rw [map_pow, hb, hz])
  have hbNorm : ‖b‖ ^ d = 1 := by rw [← norm_pow, hbPow, ha]
  exact ⟨⟨Units.mk0 b hb0, (mem_ladicUnitSphere ℓ _).mpr
    ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hd.ne').mp hbNorm)⟩, Units.ext hb⟩

/-- An unramified twist relating two transported classes comes from a unique
possible ℓ-adic parameter and relates their original Galois classes. -/
theorem exists_ladicUnramified_of_transport_twist {k : ℕ}
    (ρ σ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) (z : ℂˣ)
    (h : ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ σ) =
      twistClass (localUnramifiedCharacter K Ω z).toMonoidHom
        (ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ))) :
    ∃ χ : ladicUnramifiedCharacters K Ω ℓ,
      ladicWeilTwistParameter K Ω ℓ ι χ = z ∧ σ = ladicUnramifiedTwist K Ω ℓ k χ ρ := by
  let := ι.toAlgebra
  obtain ⟨A, hAc, _, hA, hrA⟩ := exists_ladicRepresentative K Ω ℓ ρ
  obtain ⟨B, hBc, _, hB, _⟩ := exists_ladicRepresentative K Ω ℓ σ
  have hrep := h
  rw [← hA, ← hB] at hrep
  let A' := ladicScalarExtension ℓ ι (restrict πₘ A)
  let B' := ladicScalarExtension ℓ ι (restrict πₘ B)
  let χW := localUnramifiedCharacter K Ω z
  change classOf B' = classOf (FiniteRepresentation.twist χW.toMonoidHom A') at hrep
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp hrep
  let w := localGeometricFrobenius K Ω
  let g := π w
  have hrank : Module.finrank ℂ A' = k + 1 := by
    change Module.finrank ℂ (ℂ ⊗[E] A) = k + 1
    exact Module.finrank_baseChange.trans hrA
  have hdet := congrArg (fun f : W →* ℂˣ => (f w : ℂ)) (determinantCharacter_eq e)
  change LinearMap.det (B'.representation w) =
    LinearMap.det (Langlands.twist χW.toMonoidHom A'.representation w) at hdet
  rw [Langlands.det_twist, hrank] at hdet
  have hzW : χW w = z := localUnramifiedCharacter_geometricFrobenius K Ω z
  change LinearMap.det ((B.representation g).baseChange ℂ) =
    (χW w : ℂ) ^ (k + 1) * LinearMap.det ((A.representation g).baseChange ℂ) at hdet
  rw [hzW, LinearMap.det_baseChange, LinearMap.det_baseChange] at hdet
  let δA := ladicDeterminant K Ω ℓ A hAc
  let δB := ladicDeterminant K Ω ℓ B hBc
  let a := δB g / δA g
  have ha : ‖(a : E)‖ = 1 := by
    change ‖((δB g / δA g : Eˣ) : E)‖ = 1
    rw [Units.val_div_eq_div_val, norm_div, norm_eq_one_of_compact_character δB,
      norm_eq_one_of_compact_character δA, div_one]
  have hz : (z : ℂ) ^ (k + 1) = ι (a : E) := by
    change (z : ℂ) ^ (k + 1) = ι ((δB g / δA g : Eˣ) : E)
    rw [Units.val_div_eq_div_val, map_div₀]
    exact (eq_div_iff ((map_ne_zero ι).mpr (δA g).ne_zero)).mpr hdet.symm
  obtain ⟨b, hb⟩ := exists_ladicUnit_of_power ℓ ι (Nat.succ_pos k) ha hz
  let χ := ladicUnramifiedCharacter ℓ K Ω b
  have hχ : ladicWeilTwistParameter K Ω ℓ ι χ = z := by
    change Units.map ι.toMonoidHom ((ladicUnramifiedCharacter ℓ K Ω b).val (π w)) = z
    rw [ladicUnramifiedCharacter_localProjection]
    simpa [w, localDegreeInt, localGeometricFrobenius_degree] using hb
  refine ⟨χ, hχ, ladicWeilTransport_injective K Ω ℓ ι k ?_⟩
  change ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ σ) =
    ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ
      (ladicUnramifiedTwist K Ω ℓ k χ ρ))
  rw [ladicWeilTransport_unramifiedTwist, hχ]
  exact h

end Langlands.Henniart.LocalNumerical
