import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # Locally embeddable unitary tori with a prescribed norm -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root UnitaryPoints

/-- **Construction of a locally embeddable field with involution of prescribed norm.**
Let `E/F` be a separable quadratic extension of a number field and `B` a central simple
`E`-algebra of degree `n` with an `F`-linear involution `τ` acting on `E` by the nontrivial
automorphism of `E/F`. If `z ∈ Eˣ` is, at every place `v` of `F`, the relative reduced norm of
a unit `x` of `F_v ⊗[F] B` with `x τ(x) = 1`, then there are a field extension `P/E` of
degree `n`, an `F`-linear involution `σ` of `P` acting on `E` by the nontrivial automorphism,
and `x ∈ P` with `x σ(x) = 1` and `N_{P/E}(x) = z`, such that at every place `v` there is an
injective `F_v`-algebra homomorphism `F_v ⊗[F] P → F_v ⊗[F] B` that is the identity on `E`
and intertwines `σ` and `τ`. -/
def NumberFieldUnitaryNormTorusStatement : Prop :=
  ∀ (F E B : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    (τ : FirstKindInvolution F B),
    (∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e)) →
    ∀ z : Eˣ,
      (∀ v : Global.Place F,
        ∃ x : (Global.placeCompletion F v ⊗[F] B)ˣ,
          x ∈ unitaryPoints τ (Global.placeCompletion F v) ∧
            (relativeNorm F E B (Global.placeCompletion F v) x :
                E ⊗[F] Global.placeCompletion F v) =
              (z : E) ⊗ₜ[F] (1 : Global.placeCompletion F v)) →
      ∃ (P : Type u) (_ : Field P) (_ : Algebra E P) (_ : Algebra F P)
        (_ : IsScalarTower F E P) (_ : FiniteDimensional E P)
        (σ : FirstKindInvolution F P),
        (∀ e : E, σ (algebraMap E P e) = algebraMap E P (conjugation F E e)) ∧
        Module.finrank E B = Module.finrank E P ^ 2 ∧
        (∃ x : P, x * σ x = 1 ∧ Algebra.norm E x = (z : E)) ∧
        ∀ v : Global.Place F,
          ∃ φ : Global.placeCompletion F v ⊗[F] P →ₐ[Global.placeCompletion F v]
              Global.placeCompletion F v ⊗[F] B,
            Function.Injective φ ∧
              (∀ e : E, φ ((1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E P e) =
                (1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E B e) ∧
              ∀ y : Global.placeCompletion F v ⊗[F] P,
                φ (σ.baseChange (Global.placeCompletion F v) y) =
                  τ.baseChange (Global.placeCompletion F v) (φ y)

end Langlands.CentralSimple
