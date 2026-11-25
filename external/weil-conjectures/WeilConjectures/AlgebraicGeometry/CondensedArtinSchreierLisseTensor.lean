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

/-! Tensor addition clause for the condensed Artin--Schreier sheaf.

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lemma-artin-schreier-character-sheaf--2).

The recorded `qlbarTraceSheafOf` is an abbreviation for the target condensed
Artin--Schreier sheaf.  The qlbar trace tensor theorem supplies the coherence map;
the only remaining input is the explicit trace comparison bridge for an arbitrary
character.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

/-- Tensor addition for the condensed Artin--Schreier sheaf.

Proof source: lemma-artin-schreier-character-sheaf and lemma-artin-schreier-character-sheaf.  The
bridge gives comparison isomorphisms for `f`, `g`, and `f+g`; compose these with
`AlgebraicGeometry.ArtinSchreierTrace.qlbar_artinSchreier_trace_tensor_properties`.  The equality
`a*f+a*g=a*(f+g)` is the elementary scalar distributivity step.
(blueprint: lemma-artin-schreier-character-sheaf--2).
-/
theorem condensedArtinSchreierSheafOf_tensor_addition
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) (f g : Γ(X₀, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f ⊗
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ g ≅
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (f + g)) := by
  classical
  letI : Fact (ringChar k₀).Prime := ⟨CharP.char_is_prime k₀ (ringChar k₀)⟩
  obtain ⟨Ψ, a, hΨ, hψ', hcmp, hcmpinv⟩ :=
    condensedArtinSchreier_trace_bridge k₀ ℓ X₀ ψ hψ
  obtain ⟨e⟩ :=
    (AlgebraicGeometry.ArtinSchreierTrace.qlbar_artinSchreier_trace_tensor_properties
      (ringChar k₀) ℓ
      (Fact.out : ringChar k₀ ≠ ℓ) k₀ Ψ hΨ X₀
      (scalar k₀ X₀ (a : k₀) * f) (scalar k₀ X₀ (a : k₀) * g)).1
  obtain ⟨ef⟩ := hcmp f
  obtain ⟨eg⟩ := hcmp g
  obtain ⟨efg⟩ := hcmp (f + g)
  have hadd : scalar k₀ X₀ (a : k₀) * f + scalar k₀ X₀ (a : k₀) * g =
      scalar k₀ X₀ (a : k₀) * (f + g) := by
    rw [mul_add]
  exact ⟨tensorIso ef eg ≪≫ e ≪≫
    eqToIso (congrArg (fun z ↦ qlbarTraceSheafOf (ringChar k₀) ℓ k₀ Ψ X₀ z)
      hadd) ≪≫ efg.symm⟩

end AlgebraicGeometry.ProEtale
