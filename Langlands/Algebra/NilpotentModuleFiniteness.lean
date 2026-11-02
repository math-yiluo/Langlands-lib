import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Ideal.Operations

universe u v

namespace Langlands.Algebra

open Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Generating modulo a nilpotent ideal already generates the whole module. -/
theorem eq_top_of_sup_smul_eq_top_of_nilpotent
    (I : Ideal R) (hI : IsNilpotent I) (N : Submodule R M)
    (hN : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by
  obtain ⟨n, hn⟩ := hI
  have hpow : ∀ k : ℕ, N ⊔ I ^ k • (⊤ : Submodule R M) = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          N ⊔ I ^ (k + 1) • (⊤ : Submodule R M) =
              N ⊔ I • (N ⊔ I ^ k • (⊤ : Submodule R M)) := by
                symm
                rw [smul_sup, ← sup_assoc,
                  sup_eq_left.mpr (show I • N ≤ N from Submodule.smul_le_right),
                  ← Submodule.mul_smul, ← pow_succ']
          _ = ⊤ := by rw [ih, hN]
  simpa [hn] using hpow n

/-- Lift a specified finite generating family modulo a nilpotent ideal to an
equally sized generating family of the module. -/
noncomputable def liftGeneratingFamilyOfNilpotent
    (I : Ideal R) (hI : IsNilpotent I) {n : ℕ}
    (s : Fin n → M ⧸ (I • (⊤ : Submodule R M)))
    (hs : Submodule.span R (Set.range s) = ⊤) :
    {t : Fin n → M //
      (∀ i, (I • (⊤ : Submodule R M)).mkQ (t i) = s i) ∧
        Submodule.span R (Set.range t) = ⊤} := by
  classical
  let Q := I • (⊤ : Submodule R M)
  choose t ht using fun i => Q.mkQ_surjective (s i)
  let N : Submodule R M := Submodule.span R (Set.range t)
  have hmap : N.map Q.mkQ = ⊤ := by
    change (Submodule.span R (Set.range t)).map Q.mkQ = ⊤
    rw [Submodule.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, ht] using hs
  have hN : N = ⊤ := by
    apply eq_top_of_sup_smul_eq_top_of_nilpotent I hI N
    have hc := congrArg (Submodule.comap Q.mkQ) hmap
    simpa only [Submodule.comap_map_eq, Submodule.ker_mkQ, Submodule.comap_top] using hc
  exact ⟨t, ht, hN⟩

/-- Finite generation lifts from reduction by a nilpotent ideal, without a
finiteness assumption on the ideal. -/
theorem finite_of_quotient_smul_nilpotent
    (I : Ideal R) (hI : IsNilpotent I)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Finite R M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := R) (M := M ⧸ (I • (⊤ : Submodule R M)))
  obtain ⟨t, _, ht⟩ := liftGeneratingFamilyOfNilpotent I hI s hs
  exact Module.Finite.of_fg_top (ht ▸ Submodule.fg_span (Set.finite_range t))

end Langlands.Algebra
