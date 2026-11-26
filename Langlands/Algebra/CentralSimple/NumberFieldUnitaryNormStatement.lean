import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # The unitary norm theorem over number fields -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root UnitaryPoints

/-- **The unitary norm theorem.** Let `E/F` be a separable quadratic extension of a number
field and `B` a finite-dimensional central simple `E`-algebra with an `F`-linear involution `τ`
acting on `E` by the nontrivial automorphism of `E/F`. If `z ∈ Eˣ` is, at every place `v` of
`F`, the relative reduced norm of a unit `x` of `F_v ⊗[F] B` with `x τ(x) = 1`, then
`z = Nrd(x)` for a unit `x` of `B` with `x τ(x) = 1`. -/
def NumberFieldUnitaryNormStatement : Prop :=
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
      ∃ x : Bˣ, (x : B) * τ x = 1 ∧ reducedNorm E B E ((1 : E) ⊗ₜ[E] (x : B)) = z

end Langlands.CentralSimple
