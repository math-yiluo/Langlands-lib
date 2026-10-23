import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.AdelicFunctoriality.Isomorphism
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois descent for the actual idele inclusion -/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

/-- For every Galois extension of number fields, the actual idele inclusion is
injective and its image consists exactly of the ideles fixed by all relative
automorphisms. This defines the descent proposition without proving it. -/
def IdeleGaloisDescent : Prop :=
  ∀ (K : Type u) (E : Type v) [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E] [IsGalois K E],
    Function.Injective (ideleInclusion (K := K) (L := E)) ∧
      ∀ a : IdeleGroup (𝓞 E) E,
        (∀ σ : E ≃ₐ[K] E, ideleEquiv σ.toRingEquiv a = a) ↔
          ∃ b : IdeleGroup (𝓞 K) K,
            ideleInclusion (K := K) (L := E) b = a

end Langlands.ClassField.Global
