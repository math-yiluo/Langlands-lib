import Langlands.ClassFieldTheory.Local.IntermediateNormSurjectivityStatement

/-! # Inheritance of intermediate-field norm surjectivity -/

namespace Langlands.ClassFieldTheory.Local

open Langlands.LocalClassField

private theorem norm_surjective_of_base_equiv
    (A B C : Type*) [Field A] [Field B] [Field C]
    [Algebra A C] [Algebra B C]
    [FiniteDimensional A C] [FiniteDimensional B C]
    (e : A ≃+* B)
    (he : (algebraMap B C).comp e.toRingHom = algebraMap A C)
    (hn : Function.Surjective (normUnits B C)) :
    Function.Surjective (normUnits A C) := by
  intro x
  obtain ⟨y, hy⟩ := hn (Units.map e.toMonoidHom x)
  refine ⟨y, ?_⟩
  apply Units.ext
  apply e.injective
  change e (Algebra.norm A (y : C)) = e (x : A)
  rw [Algebra.norm_eq_of_ringEquiv e he]
  exact congrArg (fun z : Bˣ => (z : B)) hy

private theorem norm_surjective_lower
    (A B C : Type*) [Field A] [Field B] [Field C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [FiniteDimensional A B] [FiniteDimensional A C] [FiniteDimensional B C]
    (hn : Function.Surjective (normUnits A C)) :
    Function.Surjective (normUnits A B) := by
  intro x
  obtain ⟨y, hy⟩ := hn x
  refine ⟨normUnits B C y, ?_⟩
  apply Units.ext
  change Algebra.norm A (Algebra.norm B (y : C)) = (x : A)
  rw [Algebra.norm_norm]
  exact congrArg (fun z : Aˣ => (z : A)) hy

/-- All four norm-surjectivity inheritance assertions for a finite extension. -/
theorem intermediateNormSurjectivityInheritance.{u} :
    IntermediateNormSurjectivityInheritance.{u} := by
  intro K L _ _ _ _ hn
  have hbase : Function.Surjective (normUnits K L) := by
    let : FiniteDimensional (⊥ : IntermediateField K L) L :=
      FiniteDimensional.right K (⊥ : IntermediateField K L) L
    apply norm_surjective_of_base_equiv K (⊥ : IntermediateField K L) L
      (IntermediateField.botEquiv K L).symm.toRingEquiv
    · ext x
      simp
    · exact hn ⊥
  refine ⟨hbase, ?_, ?_, ?_⟩
  · intro E
    let : FiniteDimensional K E := FiniteDimensional.left K E L
    let : FiniteDimensional E L := FiniteDimensional.right K E L
    exact norm_surjective_lower K E L hbase
  · intro E F
    let : FiniteDimensional K E := FiniteDimensional.left K E L
    let : FiniteDimensional F E := FiniteDimensional.right K F E
    let : FiniteDimensional E L := FiniteDimensional.right K E L
    let : FiniteDimensional F L := FiniteDimensional.right K F L
    let : FiniteDimensional (IntermediateField.lift F) L :=
      FiniteDimensional.right K (IntermediateField.lift F) L
    apply norm_surjective_lower F E L
    apply norm_surjective_of_base_equiv F (IntermediateField.lift F) L
      (IntermediateField.liftAlgEquiv F).toRingEquiv
    · ext x
      rfl
    · exact hn (IntermediateField.lift F)
  · intro E F
    exact hn (F.restrictScalars K)

end Langlands.ClassFieldTheory.Local
