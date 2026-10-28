import Langlands.Algebra.UnitizationStableGenerationStatements
import Mathlib.RingTheory.Noetherian.Basic

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationStableGeneration

universe uR uA uM

section SuppliedAction

variable (R : Type uR) (A : Type uA) (M : Type uM)
variable [CommRing R] [NonUnitalRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]
variable [AddCommGroup M] [Module R M] [Module (Unitization R A) M]
variable [IsScalarTower R (Unitization R A) M]
variable (ρ : A →ₙₐ[R] Module.End R M)
variable (hsmul : ∀ (u : Unitization R A) (m : M),
  u • m = u.fst • m + ρ u.snd m)

include hsmul

theorem fg_iff_stable_generators (Q : Submodule (Unitization R A) M) :
    Q.FG ↔ ∃ S : Finset M, (↑S : Set M) ⊆ Q ∧
      ∀ P : Submodule R M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        (↑S : Set M) ⊆ P → Q.restrictScalars R ≤ P := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_, ?_⟩
    · rw [← hS]
      exact Submodule.subset_span
    · intro P hP hSP
      let T : Submodule (Unitization R A) M :=
        { carrier := P
          zero_mem' := P.zero_mem
          add_mem' := P.add_mem
          smul_mem' := by
            intro u m hm
            rw [hsmul]
            exact P.add_mem (P.smul_mem u.fst hm) (hP u.snd m hm) }
      have hQT : Q ≤ T := by
        rw [← hS]
        exact Submodule.span_le.mpr hSP
      exact hQT
  · rintro ⟨S, hSQ, hgen⟩
    refine ⟨S, le_antisymm (Submodule.span_le.mpr hSQ) ?_⟩
    apply hgen ((Submodule.span (Unitization R A) (↑S : Set M)).restrictScalars R)
    · intro a m hm
      have h :=
        (Submodule.span (Unitization R A) (↑S : Set M)).smul_mem
          (Unitization.inr a) hm
      simpa [hsmul] using h
    · exact Submodule.subset_span

theorem finite_iff_stable_generators :
    Module.Finite (Unitization R A) M ↔
      ∃ S : Finset M, ∀ P : Submodule R M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        (↑S : Set M) ⊆ P → P = ⊤ := by
  rw [Module.finite_def, fg_iff_stable_generators R A M ρ hsmul]
  constructor
  · rintro ⟨S, _, hS⟩
    refine ⟨S, ?_⟩
    intro P hP hSP
    apply top_unique
    simpa using hS P hP hSP
  · rintro ⟨S, hS⟩
    refine ⟨S, by simp, ?_⟩
    intro P hP hSP
    rw [hS P hP hSP]
    exact le_top

theorem noetherian_iff_stable_generators :
    IsNoetherian (Unitization R A) M ↔
      ∀ P : Submodule R M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
          ∀ Q : Submodule R M,
            (∀ (a : A) (m : M), m ∈ Q → ρ a m ∈ Q) →
            (↑S : Set M) ⊆ Q → P ≤ Q := by
  constructor
  · intro hN P hP
    let T : Submodule (Unitization R A) M :=
      { carrier := P
        zero_mem' := P.zero_mem
        add_mem' := P.add_mem
        smul_mem' := by
          intro u m hm
          rw [hsmul]
          exact P.add_mem (P.smul_mem u.fst hm) (hP u.snd m hm) }
    exact (fg_iff_stable_generators R A M ρ hsmul T).mp (hN.noetherian T)
  · intro hN
    constructor
    intro T
    apply (fg_iff_stable_generators R A M ρ hsmul T).mpr
    apply hN (T.restrictScalars R)
    intro a m hm
    have h := T.smul_mem (Unitization.inr a) hm
    simpa [hsmul] using h

end SuppliedAction

theorem submoduleGeneration : SubmoduleGenerationStatement.{uR, uA, uM} := by
  intro R A M _ _ _ _ _ _ _ _ _ ρ hsmul
  exact fg_iff_stable_generators R A M ρ hsmul

theorem moduleGeneration : ModuleGenerationStatement.{uR, uA, uM} := by
  intro R A M _ _ _ _ _ _ _ _ _ ρ hsmul
  exact finite_iff_stable_generators R A M ρ hsmul

theorem noetherianGeneration : NoetherianGenerationStatement.{uR, uA, uM} := by
  intro R A M _ _ _ _ _ _ _ _ _ ρ hsmul
  exact noetherian_iff_stable_generators R A M ρ hsmul

theorem unitizationStableGeneration : UnitizationStableGenerationStatement.{uR, uA, uM} :=
  ⟨submoduleGeneration, moduleGeneration, noetherianGeneration⟩

end Langlands.Algebra.UnitizationStableGeneration
