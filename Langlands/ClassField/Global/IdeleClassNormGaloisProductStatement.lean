import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.ClassField.Global.Cocycle
import Mathlib.FieldTheory.Galois.Basic

/-! # The idele-class norm as a product of Galois conjugates -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField BigOperators
open Langlands.Global.AdelicFunctoriality

universe u v

/-- For a Galois extension of number fields, the norm of an idele class, included
back into the upper idele-class group, equals the product of all its conjugates. -/
def IdeleClassNormGaloisProduct : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L],
    letI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite (L ≃ₐ[K] L)
    ∀ x : IdeleClassGroup (𝓞 L) L,
      ideleClassInclusion (K := K) (L := L) (ideleClassNorm (K := K) (L := L) x) =
        ∏ σ : L ≃ₐ[K] L, relativeIdeleClassAut K L σ x

end Langlands.ClassField.Global
