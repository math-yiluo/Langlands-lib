import Langlands.ClassField.Global.Cocycle
import Langlands.Global.AdelicFunctoriality.Inclusion
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois descent for the actual idele-class inclusion -/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

/-- For every Galois extension of number fields, the actual idele-class inclusion
is injective and its image consists exactly of the classes fixed by the actual
relative automorphism action. This is a statement, not a proof of descent. -/
def IdeleClassGaloisDescent : Prop :=
  ∀ (K : Type u) (E : Type v) [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E] [IsGalois K E],
    Function.Injective (ideleClassInclusion (K := K) (L := E)) ∧
      ∀ c : IdeleClassGroup (𝓞 E) E,
        (∀ σ : E ≃ₐ[K] E, relativeIdeleClassAut K E σ c = c) ↔
          ∃ a : IdeleClassGroup (𝓞 K) K,
            ideleClassInclusion (K := K) (L := E) a = c

end Langlands.ClassField.Global
