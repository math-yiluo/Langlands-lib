import Langlands.Algebra.IntegerOriginalSubmoduleGenerationStatements

set_option autoImplicit false

namespace Langlands.Algebra.IntegerOriginalSubmoduleGeneration

universe uA uM

section OriginalAction

variable {A : Type uA} {M : Type uM}
variable [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]

/-- Finite generation of the actual unitized submodule of an original stable additive
subgroup is finite stable generation among the original stable additive subgroups. -/
theorem fg_intUnitizedOrderIso_iff (P : NonUnitalSubmodule A M) :
    (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        (NonUnitalSubmodule.intUnitizedOrderIso P).FG) ↔
      ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
        ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q := by
  let _ := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_, fun Q hSQ => ?_⟩
    · have h : (↑S : Set M) ⊆ Submodule.span (Unitization ℤ A) (↑S : Set M) :=
        Submodule.subset_span
      rw [hS] at h
      exact h
    · rw [← NonUnitalSubmodule.intUnitizedOrderIso.le_iff_le, ← hS, Submodule.span_le]
      exact hSQ
  · rintro ⟨S, hSP, hmin⟩
    refine ⟨S, le_antisymm (Submodule.span_le.2 hSP) ?_⟩
    have h := hmin
      (NonUnitalSubmodule.intUnitizedOrderIso.symm
        (Submodule.span (Unitization ℤ A) (↑S : Set M)))
      (Submodule.subset_span (R := Unitization ℤ A) (s := (↑S : Set M)))
    rwa [← NonUnitalSubmodule.intUnitizedOrderIso.le_iff_le,
      OrderIso.apply_symm_apply] at h

/-- The actual unitized module is finite exactly when a finite set generates the whole
carrier among the original stable additive subgroups. -/
theorem finite_iff_original_stable_generators :
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
      Module.Finite (Unitization ℤ A) M) ↔
    ∃ S : Finset M, ∀ P : NonUnitalSubmodule A M,
      (↑S : Set M) ⊆ P → ∀ m : M, m ∈ P := by
  let _ := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
  rw [Module.finite_def, ← NonUnitalSubmodule.intUnitizedOrderIso.apply_symm_apply ⊤,
    fg_intUnitizedOrderIso_iff]
  constructor
  · rintro ⟨S, -, hS⟩
    exact ⟨S, fun P hSP m => hS P hSP (Submodule.mem_top (R := Unitization ℤ A) (x := m))⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, fun _ _ => Submodule.mem_top (R := Unitization ℤ A), fun P hSP m _ => hS P hSP m⟩

/-- Noetherianity of the actual unitized module is finite stable generation of every
original stable additive subgroup. -/
theorem noetherian_iff_original_stable_generators :
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
      IsNoetherian (Unitization ℤ A) M) ↔
    ∀ P : NonUnitalSubmodule A M,
      ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
        ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q := by
  let _ := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
  constructor
  · intro hN P
    exact (fg_intUnitizedOrderIso_iff P).1 (hN.noetherian _)
  · intro hP
    refine ⟨fun N => ?_⟩
    rw [← NonUnitalSubmodule.intUnitizedOrderIso.apply_symm_apply N]
    exact (fg_intUnitizedOrderIso_iff _).2 (hP _)

end OriginalAction

theorem submoduleGeneration : SubmoduleGenerationStatement.{uA, uM} :=
  fun _ _ _ _ _ P => fg_intUnitizedOrderIso_iff P

theorem moduleGeneration : ModuleGenerationStatement.{uA, uM} :=
  fun _ _ _ _ _ => finite_iff_original_stable_generators

theorem noetherianGeneration : NoetherianGenerationStatement.{uA, uM} :=
  fun _ _ _ _ _ => noetherian_iff_original_stable_generators

/-- The submodule, whole-module and Noetherian comparisons, in that order. -/
theorem integerOriginalSubmoduleGeneration :
    IntegerOriginalSubmoduleGenerationStatement.{uA, uM} :=
  ⟨submoduleGeneration, moduleGeneration, noetherianGeneration⟩

end Langlands.Algebra.IntegerOriginalSubmoduleGeneration
