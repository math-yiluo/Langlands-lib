import Langlands.Global.AdelicGroupLocalPoints

/-! # The local–global principle for embeddings of maximal subfields -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

/-- **The local–global principle for embeddings of maximal subfields.** Let `F` be a number
field, `E/F` a finite extension, `B` a finite-dimensional central simple `E`-algebra that is
an `F`-algebra through `E`, and `P/E` a field extension with `[B : E] = [P : E]²`. If at every
place `v` of `F` there is an injective `F_v`-algebra homomorphism `F_v ⊗[F] P → F_v ⊗[F] B`
that is the identity on `E`, then there is an `E`-algebra homomorphism `P → B`. -/
def NumberFieldLocalGlobalEmbeddingStatement : Prop :=
  ∀ (F E B P : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P] [FiniteDimensional E P],
    Module.finrank E B = Module.finrank E P ^ 2 →
    (∀ v : Global.Place F,
      ∃ φ : Global.placeCompletion F v ⊗[F] P →ₐ[Global.placeCompletion F v]
          Global.placeCompletion F v ⊗[F] B,
        Function.Injective φ ∧
          ∀ e : E, φ ((1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E P e) =
            (1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E B e) →
    Nonempty (P →ₐ[E] B)

end Langlands.CentralSimple
