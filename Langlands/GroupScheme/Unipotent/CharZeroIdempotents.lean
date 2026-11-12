import Langlands.GroupScheme.Unipotent.CharZeroPeriodic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Locally unipotent automorphisms fix idempotents in characteristic zero

Noetherian spaces have finitely many clopen subsets. Consequently a Noetherian
ring has finitely many idempotents, and a locally unipotent automorphism of an
algebra over a characteristic-zero field fixes them.
-/

noncomputable section

namespace Langlands.GroupScheme.Unipotent

open TopologicalSpace

/-- A clopen set is determined by the irreducible components it contains. -/
theorem finite_clopens_of_noetherian (X : Type*) [TopologicalSpace X]
    [NoetherianSpace X] : Finite (Clopens X) := by
  classical
  let : Finite (irreducibleComponents X) :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  let φ : Clopens X → Set (irreducibleComponents X) :=
    fun s => {C | C.val ⊆ (s : Set X)}
  have hle : ∀ s t : Clopens X, φ s = φ t → s ≤ t := by
    intro s t h x hx
    let C : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hs : C.val ⊆ (s : Set X) :=
      isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_isClopen s.isClopen
        ⟨x, mem_irreducibleComponent, hx⟩
    have ht : C.val ⊆ (t : Set X) := by
      change C ∈ φ t
      rw [← h]
      exact hs
    exact ht mem_irreducibleComponent
  exact Finite.of_injective φ fun s t h => le_antisymm (hle s t h) (hle t s h.symm)

/-- A commutative Noetherian ring has only finitely many idempotents. -/
theorem finite_idempotents_of_noetherian (B : Type*) [CommRing B] [IsNoetherianRing B] :
    Finite {b : B // IsIdempotentElem b} := by
  let := finite_clopens_of_noetherian (PrimeSpectrum B)
  exact Finite.of_injective (PrimeSpectrum.isIdempotentElemEquivClopens (R := B))
    (PrimeSpectrum.isIdempotentElemEquivClopens (R := B)).injective

variable {k B : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]

/-- If an algebra has finitely many idempotents, an algebra endomorphism with an
algebra endomorphism as right inverse, and which is locally unipotent as a linear
map, fixes every idempotent. -/
theorem idempotent_fixed_of_locally_unipotent
    [Finite {b : B // IsIdempotentElem b}]
    (τ σ : B →ₐ[k] B) (hτσ : Function.RightInverse σ τ)
    (hu : ∀ b : B, ∃ m : ℕ, ((τ.toLinearMap - 1) ^ m) b = 0)
    {b : B} (hb : IsIdempotentElem b) : τ b = b := by
  let I := {b : B // IsIdempotentElem b}
  let T : I → I := fun b => ⟨τ b, b.property.map τ⟩
  have hsurj : Function.Surjective T := by
    intro c
    exact ⟨⟨σ c, c.property.map σ⟩, Subtype.ext (hτσ c)⟩
  have hinj : Function.Injective T := Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨n, hn, hperiodic⟩ := hinj.mem_periodicPts (⟨b, hb⟩ : I)
  have hsem : Function.Semiconj (fun c : I => (c : B)) T τ.toLinearMap := fun _ => rfl
  have hperiodic' := hperiodic.map hsem
  change (τ.toLinearMap : B → B)^[n] b = b at hperiodic'
  have hperiod : (τ.toLinearMap ^ n) b = b := by
    simpa only [Module.End.pow_apply] using hperiodic'
  obtain ⟨m, hm⟩ := hu b
  exact apply_eq_self_of_periodic_of_pow_sub_one_eq_zero (Nat.ne_of_gt hn) hperiod hm

end Langlands.GroupScheme.Unipotent
