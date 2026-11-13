import Langlands.Representation.Whittaker.LastEntryOneAssembly
import Langlands.AllField.Representation.RankinSelberg.RootCoordinateProof
import Langlands.AllField.Representation.Whittaker.LastEntryOneAsymptoticStatement
/-!
# Coordinates and scalar assembly for the last-entry-one expansion

Coordinate and scalar-functional bookkeeping used by the closed proof in
`LastEntryOneAsymptoticProof`. The assembly helper takes a root expansion as input.
-/

noncomputable section

namespace Langlands.AllField.WhittakerLastEntryOne
open Langlands.WhittakerLastEntryOne hiding assemble pullback_injective rootHom_rootLift rootLift_last rootLift_rootHom
open Langlands.AllField.WhittakerLastEntryOne

open scoped BigOperators

universe uF uV uA

section Algebra

variable {K : Type uF} [Field K] {n : ℕ}

variable [TopologicalSpace K] [IsTopologicalRing K]

end Algebra

section Padic

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ)

include T

/-- The existing full coordinate theorem recovers every root of this section. -/
theorem rootHom_rootLift (x : Fin n → Fˣ) :
    rootHom (rootLift x) = x := by
  have h := (Langlands.AllField.RankinSelberg.rootCoordinateChange F T n).2.2.1
    (Fin.lastCases 1 x)
  funext i
  have hi := congrArg (fun a => a i.castSucc) h
  simpa only [rootHom, MonoidHom.coe_mk, OneHom.coe_mk,
    rootLift, Fin.lastCases_castSucc] using hi

/-- The cumulative-product section has last entry one, also when `n = 0`. -/
theorem rootLift_last (x : Fin n → Fˣ) :
    rootLift x (Fin.last n) = 1 := by
  have h := ((Langlands.AllField.RankinSelberg.rootCoordinateChange F T n).2.2.2.2.2.2
    (Fin.lastCases 1 x)).2.1
  simpa only [rootLift, Fin.lastCases_last] using h

/-- Every last-entry-one diagonal is recovered from its simple roots. -/
theorem rootLift_rootHom (a : Fin (n + 1) → Fˣ)
    (ha : a (Fin.last n) = 1) :
    rootLift (rootHom a) = a := by
  have h := (Langlands.AllField.RankinSelberg.rootCoordinateChange F T n).2.2.2.1 a
  change (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·),
    Fin.lastCases 1 (fun k => a k.castSucc / a k.succ) j) = a
  simpa only [ha] using h

/-- Pullback has no collisions because the root map has a section. -/
theorem pullback_injective :
    Function.Injective (fun f : (Fin n → Fˣ) → ℂ =>
      fun a : Fin (n + 1) → Fˣ => f (rootHom a)) := by
  intro f g h
  funext x
  have hx := congrFun h (rootLift x)
  simpa only [rootHom_rootLift F T n] using hx

/-- A uniform root-coordinate expansion for one spanning functional gives
the target's finite set on the full torus, uniformly for all functionals. -/
theorem assemble
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (eligible : Module.Dual ℂ V → Prop) (ℓ₀ : Module.Dual ℂ V)
    (hspan : ∀ ℓ, eligible ℓ → ∃ c : ℂ, ℓ = c • ℓ₀) :
    letI := T.topology
    ∀ (X : Finset ((Fin n → Fˣ) → ℂ)),
      (∀ χ ∈ X, IsFiniteFunction χ) →
      (∀ v : V, ∃ φ : ((Fin n → Fˣ) → ℂ) →
          HarmonicAnalysis.SchwartzBruhat (Fin n → F),
        ∀ x, ℓ₀ (ρ (torus (rootLift x)) v) =
          ∑ χ ∈ X, φ χ (fun i => (x i : F)) * χ x) →
      ∃ Y : Finset ((Fin (n + 1) → Fˣ) → ℂ),
        (∀ χ ∈ Y, IsFiniteFunction χ) ∧
        ∀ ℓ, eligible ℓ → ∀ v : V,
          ∃ Φ : ((Fin (n + 1) → Fˣ) → ℂ) →
              HarmonicAnalysis.SchwartzBruhat (Fin n → F),
            ∀ a, a (Fin.last n) = 1 →
              ℓ (ρ (torus a) v) = ∑ χ ∈ Y, Φ χ (roots a) * χ a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro X hX hroot
  classical
  let pull : ((Fin n → Fˣ) → ℂ) →
      ((Fin (n + 1) → Fˣ) → ℂ) := fun χ a => χ (rootHom a)
  have hpull : Function.Injective pull := pullback_injective F T n
  have hleft (χ : (Fin n → Fˣ) → ℂ) :
      (fun x => pull χ (rootLift x)) = χ := by
    funext x
    exact congrArg χ (rootHom_rootLift F T n x)
  refine ⟨X.image pull, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hχ
    exact finiteFunction_pullback (hX ξ hξ)
  · intro ℓ hℓ v
    obtain ⟨c, rfl⟩ := hspan ℓ hℓ
    obtain ⟨φ, hφ⟩ := hroot v
    refine ⟨fun χ => c • φ (fun x => χ (rootLift x)), ?_⟩
    intro a ha
    change c * ℓ₀ (ρ (torus a) v) = _
    have heq := hφ (rootHom a)
    rw [rootLift_rootHom F T n a ha] at heq
    rw [heq, Finset.mul_sum]
    rw [Finset.sum_image (fun χ _ ξ _ h => hpull h)]
    apply Finset.sum_congr rfl
    intro χ hχ
    dsimp only
    rw [hleft]
    change c * (φ χ (roots a) * χ (rootHom a)) =
      (c * φ χ (roots a)) * χ (rootHom a)
    exact (mul_assoc _ _ _).symm

end Padic

end Langlands.AllField.WhittakerLastEntryOne
