import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # Landherr's theorem over number fields -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

/-- **Landherr's theorem.** Let `E/F` be a separable quadratic extension of a number field and
`B` a finite-dimensional central simple `E`-algebra with an `F`-linear involution `τ` acting on
`E` by the nontrivial automorphism of `E/F` (an involution of the second kind). If a symmetric
unit `y` of `B` has the form `x τ(x)` with `x` a unit of `F_v ⊗[F] B` at every place `v` of `F`,
then `y = x τ(x)` for a unit `x` of `B`. -/
def NumberFieldLandherrStatement : Prop :=
  ∀ (F E B : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    (τ : FirstKindInvolution F B),
    (∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e)) →
    ∀ y : Bˣ, τ (y : B) = y →
      (∀ v : Global.Place F,
        ∃ x : (Global.placeCompletion F v ⊗[F] B)ˣ,
          (1 : Global.placeCompletion F v) ⊗ₜ[F] (y : B) =
            (x : Global.placeCompletion F v ⊗[F] B) *
              τ.baseChange (Global.placeCompletion F v) x) →
      ∃ x : Bˣ, (y : B) = x * τ x

end Langlands.CentralSimple
