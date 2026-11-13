import Langlands.Algebra.IdempotentedDirectLimitStatements
import Langlands.Algebra.CountableSupportAlgebra
import Mathlib.Analysis.Complex.Cardinality

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

/-- Renard I.1.4: a regular module can have a degenerate completion. -/
theorem leftLimitNotNondegenerateStatement : LeftLimitNotNondegenerateStatement := by
  let : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let A := CountableSupportAlgebra.Carrier ℂ ℂ
  let : NonUnitalModule A A := NonUnitalModule.regular A
  let hA : IsIdempotented A := CountableSupportAlgebra.isIdempotented
  have hM : IsNondegenerate A A := by
    intro a
    obtain ⟨e, he⟩ := hA.exists_mem_corner a
    exact ⟨e, ((Idempotent.mem_corner_iff e a).mp he).1⟩
  refine ⟨A, inferInstance, hA, A, inferInstance, inferInstance, hM, ?_⟩
  let x : NonUnitalModuleLeftLimit A A :=
    ⟨fun e => (e : A), by
      constructor
      · intro e
        exact e.property.eq
      · intro e f hef
        exact ((Idempotent.le_iff_mul e f).mp hef).2⟩
  let := NonUnitalModuleLeftLimit.nonUnitalModule (M := A) hA
  intro hdeg
  obtain ⟨f, hf⟩ := hdeg x
  have hx : NonUnitalModuleLeftLimit.canonical (A := A) (f : A) = x :=
    (NonUnitalModuleLeftLimit.idempotent_smul hA f x).symm.trans hf
  have hright (e : Idempotent A) : (e : A) * (f : A) = (e : A) :=
    congrArg (fun y : NonUnitalModuleLeftLimit A A => y.val e) hx
  apply CountableSupportAlgebra.no_left_identity (R := ℂ) (X := ℂ)
  refine ⟨(f : A), fun a => ?_⟩
  obtain ⟨e, he⟩ := hA.exists_mem_corner a
  have hae : a * (e : A) = a := ((Idempotent.mem_corner_iff e a).mp he).2
  calc
    (f : A) * a = a * f := mul_comm _ _
    _ = (a * e) * f := congrArg (fun b : A => b * f) hae.symm
    _ = a * ((e : A) * f) := mul_assoc _ _ _
    _ = a := by rw [hright e, hae]

end Langlands.Algebra
