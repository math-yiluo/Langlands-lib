import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # Global symmetric twists of an embedding with everywhere local unitary solutions -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

/-- **Global fixed-field twists with everywhere local unitary solutions.** Let `E/F` be a
separable quadratic extension of a number field, `B` a central simple `E`-algebra of degree
`n` with an `F`-linear involution `τ` acting on `E` by the nontrivial automorphism of `E/F`,
`P/E` a field extension of degree `n` with an `F`-linear involution `σ` acting on `E` in the
same way, `ε : P → B` an `E`-algebra homomorphism, and `g` a unit of `B` with `τ g = g` and
`τ (ε p) = g ε(σ p) g⁻¹` for `p ∈ P`. Suppose that at every place `v` of `F` there are a
`σ`-fixed unit `a_v` of `F_v ⊗[F] P` and a unit `h_v` of `F_v ⊗[F] B` with
`g ε(a_v) = h_v τ(h_v)`. Then there is a nonzero `σ`-fixed `a ∈ P` such that at every place
`v` the element `g ε(a)` has the form `h τ(h)` with `h` a unit of `F_v ⊗[F] B`. -/
def NumberFieldUnitaryEmbeddingClassStatement : Prop :=
  ∀ (F E B P : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P] [FiniteDimensional E P]
    (τ : FirstKindInvolution F B) (σ : FirstKindInvolution F P),
    (∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e)) →
    (∀ e : E, σ (algebraMap E P e) = algebraMap E P (conjugation F E e)) →
    Module.finrank E B = Module.finrank E P ^ 2 →
    ∀ (ε : P →ₐ[E] B) (g : Bˣ), τ (g : B) = g →
      (∀ p : P, τ (ε p) = (g : B) * ε (σ p) * ↑g⁻¹) →
      (∀ v : Global.Place F,
        ∃ a : (Global.placeCompletion F v ⊗[F] P)ˣ,
          σ.baseChange (Global.placeCompletion F v) a = a ∧
          ∃ h : (Global.placeCompletion F v ⊗[F] B)ˣ,
            (1 : Global.placeCompletion F v) ⊗ₜ[F] (g : B) *
                Algebra.TensorProduct.map (AlgHom.id (Global.placeCompletion F v)
                  (Global.placeCompletion F v)) (ε.restrictScalars F) a =
              h * τ.baseChange (Global.placeCompletion F v) h) →
      ∃ a : P, a ≠ 0 ∧ σ a = a ∧
        ∀ v : Global.Place F,
          ∃ h : (Global.placeCompletion F v ⊗[F] B)ˣ,
            (1 : Global.placeCompletion F v) ⊗ₜ[F] ((g : B) * ε a) =
              h * τ.baseChange (Global.placeCompletion F v) h

end Langlands.CentralSimple
