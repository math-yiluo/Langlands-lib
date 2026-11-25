/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierTraceBridge
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections

/-! Inverse and inverse-character clauses for the condensed Artin--Schreier sheaf.
Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lemma-artin-schreier-character-sheaf--2). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra
namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

-- The four-way categorical tensor transport needs extra elaboration heartbeats.
/-- Tensor inverse and inverse-character identifications.

The comparison bridge reduces to the qlbar trace model, where
`qlbar_artinSchreier_trace_tensor_properties` gives both tensor orders and the
inverse-character map.  The only postponed input is the bridge itself.
(blueprint: lemma-artin-schreier-character-sheaf--2). -/
theorem condensedArtinSchreierSheafOf_inverse
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) (f : Γ(X₀, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f ⊗
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (-f) ≅
      Mod.regular (condensedRingObj
        (Profinite.padicAlgClRingObj ℓ) X₀)) ∧
    Nonempty (condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (-f) ≅
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ⁻¹ f) := by
  classical
  letI : Fact (ringChar k₀).Prime := ⟨CharP.char_is_prime k₀ (ringChar k₀)⟩
  obtain ⟨Ψ, a, hΨ, hψ', hcmp, hcmpinv⟩ :=
    condensedArtinSchreier_trace_bridge k₀ ℓ X₀ ψ hψ
  obtain ⟨⟨eadd⟩, ⟨einv⟩, ⟨einv'⟩, ⟨echar⟩⟩ :=
    AlgebraicGeometry.ArtinSchreierTrace.qlbar_artinSchreier_trace_tensor_properties (ringChar k₀) ℓ
      (Fact.out : ringChar k₀ ≠ ℓ) k₀ Ψ hΨ X₀
      (scalar k₀ X₀ (a : k₀) * f) (scalar k₀ X₀ (a : k₀) * (-f))
  obtain ⟨ef⟩ := hcmp f
  obtain ⟨eneg⟩ := hcmp (-f)
  obtain ⟨einvψ⟩ := hcmpinv f
  have hneg : scalar k₀ X₀ (a : k₀) * (-f) =
      -(scalar k₀ X₀ (a : k₀) * f) := by
    rw [mul_neg]
  let enegTrace := eqToIso (congrArg
    (fun z ↦ qlbarTraceSheafOf (ringChar k₀) ℓ k₀ Ψ X₀ z) hneg)
  refine ⟨⟨tensorIso ef eneg ≪≫ tensorIso (Iso.refl _) enegTrace ≪≫ einv⟩, ?_⟩
  exact ⟨eneg ≪≫ enegTrace ≪≫ echar.symm ≪≫ einvψ.symm⟩

end AlgebraicGeometry.ProEtale
