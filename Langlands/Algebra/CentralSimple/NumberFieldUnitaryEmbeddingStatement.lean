import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # Embeddings of fields with involution into algebras with unitary involution -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

/-- **The local–global principle for embeddings of fields with involution, unitary case.**
Let `E/F` be a separable quadratic extension of a number field, `B` a central simple
`E`-algebra of degree `n` with an `F`-linear involution `τ` acting on `E` by the nontrivial
automorphism of `E/F`, and `P/E` a field extension of degree `n` with an `F`-linear involution
`σ` acting on `E` in the same way. If at every place `v` of `F` there is an injective
`F_v`-algebra homomorphism `F_v ⊗[F] P → F_v ⊗[F] B` that is the identity on `E` and
intertwines `σ` and `τ`, then there is an `E`-algebra homomorphism `φ : P → B` with
`φ ∘ σ = τ ∘ φ`. -/
def NumberFieldUnitaryEmbeddingStatement : Prop :=
  ∀ (F E B P : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P] [FiniteDimensional E P]
    (τ : FirstKindInvolution F B) (σ : FirstKindInvolution F P),
    (∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e)) →
    (∀ e : E, σ (algebraMap E P e) = algebraMap E P (conjugation F E e)) →
    Module.finrank E B = Module.finrank E P ^ 2 →
    (∀ v : Global.Place F,
      ∃ φ : Global.placeCompletion F v ⊗[F] P →ₐ[Global.placeCompletion F v]
          Global.placeCompletion F v ⊗[F] B,
        Function.Injective φ ∧
          (∀ e : E, φ ((1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E P e) =
            (1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E B e) ∧
          ∀ y : Global.placeCompletion F v ⊗[F] P,
            φ (σ.baseChange (Global.placeCompletion F v) y) =
              τ.baseChange (Global.placeCompletion F v) (φ y)) →
    ∃ φ : P →ₐ[E] B, ∀ p : P, φ (σ p) = τ (φ p)

end Langlands.CentralSimple
