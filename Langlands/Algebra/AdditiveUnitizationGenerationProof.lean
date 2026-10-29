import Langlands.Algebra.AdditiveUnitizationGenerationStatements
import Mathlib.RingTheory.Noetherian.Basic

set_option autoImplicit false

namespace Langlands.Algebra.AdditiveUnitizationGeneration

universe uA uM

section SuppliedAction

variable (A : Type uA) (M : Type uM)
variable [NonUnitalRing A] [AddCommGroup M] [Module (Unitization ℤ A) M]
variable (ρ : A →ₙ+* AddMonoid.End M)
variable (hsmul : ∀ (u : Unitization ℤ A) (m : M),
  u • m = u.fst • m + ρ u.snd m)

include hsmul

theorem fg_iff_additive_stable_generators (Q : Submodule (Unitization ℤ A) M) :
    Q.FG ↔ ∃ S : Finset M, (↑S : Set M) ⊆ Q ∧
      ∀ P : AddSubgroup M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        (↑S : Set M) ⊆ P →
          Submodule.toAddSubgroup (R := Unitization ℤ A) Q ≤ P := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_, ?_⟩
    · rw [← hS]
      exact Submodule.subset_span
    · intro P hP hSP
      let T : Submodule (Unitization ℤ A) M :=
        { carrier := P
          zero_mem' := P.zero_mem
          add_mem' := P.add_mem
          smul_mem' := by
            intro u m hm
            rw [hsmul]
            exact P.add_mem (P.zsmul_mem hm u.fst) (hP u.snd m hm) }
      have hQT : Q ≤ T := by
        rw [← hS]
        exact Submodule.span_le.mpr hSP
      exact hQT
  · rintro ⟨S, hSQ, hgen⟩
    refine ⟨S, le_antisymm (Submodule.span_le.mpr hSQ) ?_⟩
    apply hgen (Submodule.toAddSubgroup (R := Unitization ℤ A)
      (Submodule.span (Unitization ℤ A) (↑S : Set M)))
    · intro a m hm
      have h :=
        (Submodule.span (Unitization ℤ A) (↑S : Set M)).smul_mem
          (Unitization.inr a) hm
      simpa [hsmul] using h
    · exact Submodule.subset_span

theorem finite_iff_additive_stable_generators :
    Module.Finite (Unitization ℤ A) M ↔
      ∃ S : Finset M, ∀ P : AddSubgroup M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        (↑S : Set M) ⊆ P → P = ⊤ := by
  rw [Module.finite_def, fg_iff_additive_stable_generators A M ρ hsmul]
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

theorem noetherian_iff_additive_stable_generators :
    IsNoetherian (Unitization ℤ A) M ↔
      ∀ P : AddSubgroup M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
          ∀ Q : AddSubgroup M,
            (∀ (a : A) (m : M), m ∈ Q → ρ a m ∈ Q) →
            (↑S : Set M) ⊆ Q → P ≤ Q := by
  constructor
  · intro hN P hP
    let T : Submodule (Unitization ℤ A) M :=
      { carrier := P
        zero_mem' := P.zero_mem
        add_mem' := P.add_mem
        smul_mem' := by
          intro u m hm
          rw [hsmul]
          exact P.add_mem (P.zsmul_mem hm u.fst) (hP u.snd m hm) }
    exact (fg_iff_additive_stable_generators A M ρ hsmul T).mp (hN.noetherian T)
  · intro hN
    constructor
    intro T
    apply (fg_iff_additive_stable_generators A M ρ hsmul T).mpr
    apply hN (Submodule.toAddSubgroup (R := Unitization ℤ A) T)
    intro a m hm
    have h := T.smul_mem (Unitization.inr a) hm
    simpa [hsmul] using h

end SuppliedAction

theorem submoduleGeneration : SubmoduleGenerationStatement.{uA, uM} := by
  intro A M _ _ _ ρ hsmul
  exact fg_iff_additive_stable_generators A M ρ hsmul

theorem moduleGeneration : ModuleGenerationStatement.{uA, uM} := by
  intro A M _ _ _ ρ hsmul
  exact finite_iff_additive_stable_generators A M ρ hsmul

theorem noetherianGeneration : NoetherianGenerationStatement.{uA, uM} := by
  intro A M _ _ _ ρ hsmul
  exact noetherian_iff_additive_stable_generators A M ρ hsmul

theorem additiveUnitizationGeneration : AdditiveUnitizationGenerationStatement.{uA, uM} :=
  ⟨submoduleGeneration, moduleGeneration, noetherianGeneration⟩

end Langlands.Algebra.AdditiveUnitizationGeneration
