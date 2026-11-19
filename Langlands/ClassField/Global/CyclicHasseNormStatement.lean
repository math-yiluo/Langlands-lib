import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The cyclic Hasse norm theorem for principal ideles -/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u

/-- If a principal idele is the norm of an idele in a cyclic Galois extension,
its defining field unit is the norm of a field unit. -/
def CyclicHasseNormStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (a : Fˣ) (b : IdeleGroup (𝓞 E) E),
    ideleNorm (K := F) b = IdeleGroup.unitEmbedding (𝓞 F) F a →
      ∃ x : Eˣ, Units.map (Algebra.norm F) x = a

end Langlands.ClassField.Global
