import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # Regular local unitary elements of prescribed relative reduced norm -/

universe u

open scoped TensorProduct
open Polynomial

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root UnitaryPoints

/-- **Regular local unitary elements of prescribed relative reduced norm.**
Let `E/F` be a separable quadratic extension of a number field, `B` a central simple
`E`-algebra of degree `n` with an `F`-linear involution `τ` acting on `E` by the nontrivial
automorphism `e ↦ ē`, and `v` a place of `F` with completion `F_v`. Write
`ψ : F_v ⊗[F] E → F_v ⊗[F] B` for `id ⊗ (E → B)` and `τ_v = τ.baseChange F_v`. If `z ∈ Eˣ` is
the relative reduced norm of a unit `x` of `F_v ⊗[F] B` with `x τ_v(x) = 1`, then there are
`x ∈ F_v ⊗[F] B` with `x τ_v(x) = 1` and a monic polynomial `f` of degree `n` over
`F_v ⊗[F] E` such that

* `f` is conjugate-reciprocal for `z`: `f_{n-i} = (-1)ⁿ (1 ⊗ z) (id ⊗ conj)(f_i)` for
  `0 ≤ i ≤ n`, where `f_i` is the coefficient of `Xⁱ`;
* `f(x) = 0` and `f'(x)` is a unit, the polynomials being evaluated through `ψ`;
* the elements `1, x, …, x^{n-1}` are linearly independent over `F_v ⊗[F] E` acting
  through `ψ`: `∑_{i<n} ψ(c_i) xⁱ = 0` only for `c = 0`. -/
def NumberFieldUnitaryRegularLocalStatement : Prop :=
  ∀ (F E B : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    (τ : FirstKindInvolution F B),
    (∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e)) →
    ∀ (n : ℕ), Module.finrank E B = n ^ 2 →
    ∀ (z : Eˣ) (v : Global.Place F),
      (∃ x : (Global.placeCompletion F v ⊗[F] B)ˣ,
        x ∈ unitaryPoints τ (Global.placeCompletion F v) ∧
          (relativeNorm F E B (Global.placeCompletion F v) x :
              E ⊗[F] Global.placeCompletion F v) =
            (z : E) ⊗ₜ[F] (1 : Global.placeCompletion F v)) →
      ∃ (x : Global.placeCompletion F v ⊗[F] B)
        (f : (Global.placeCompletion F v ⊗[F] E)[X]),
        x * τ.baseChange (Global.placeCompletion F v) x = 1 ∧
        f.Monic ∧ f.natDegree = n ∧
        (∀ i ≤ n, f.coeff (n - i) =
          (-1) ^ n * ((1 : Global.placeCompletion F v) ⊗ₜ[F] (z : E)) *
            Algebra.TensorProduct.map
              (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
              (conjugation F E).toAlgHom (f.coeff i)) ∧
        f.eval₂ (Algebra.TensorProduct.map
            (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
            (IsScalarTower.toAlgHom F E B) :
              Global.placeCompletion F v ⊗[F] E →+* Global.placeCompletion F v ⊗[F] B) x = 0 ∧
        IsUnit ((derivative f).eval₂ (Algebra.TensorProduct.map
            (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
            (IsScalarTower.toAlgHom F E B) :
              Global.placeCompletion F v ⊗[F] E →+* Global.placeCompletion F v ⊗[F] B) x) ∧
        ∀ c : Fin n → Global.placeCompletion F v ⊗[F] E,
          ∑ i, Algebra.TensorProduct.map
              (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
              (IsScalarTower.toAlgHom F E B) (c i) * x ^ (i : ℕ) = 0 → c = 0

end Langlands.CentralSimple
