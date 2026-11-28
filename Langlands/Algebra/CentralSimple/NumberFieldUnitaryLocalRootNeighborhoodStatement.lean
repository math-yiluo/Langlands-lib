import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.RingTheory.TensorProduct.Free

/-! # Unitary roots of nearby conjugate-reciprocal polynomials -/

universe u

open scoped TensorProduct
open Polynomial

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

/-- **Unitary roots of nearby conjugate-reciprocal polynomials (unitary Krasner lemma).**
Let `E/F` be a separable quadratic extension of a number field, `B` a central simple
`E`-algebra of degree `n` with an `F`-linear involution `τ` acting on `E` by the nontrivial
automorphism `e ↦ ē`, `v` a place of `F` with completion `F_v`, and `b` an `F`-basis of `E`.
Write `ψ : F_v ⊗[F] E → F_v ⊗[F] B` for `id ⊗ (E → B)` and `τ_v = τ.baseChange F_v`; call a
monic polynomial `g` of degree `n` over `F_v ⊗[F] E` conjugate-reciprocal (for `z ∈ E`) when
`g_{n-i} = (-1)ⁿ (1 ⊗ z) (id ⊗ conj)(g_i)` for `0 ≤ i ≤ n`, `g_i` being the coefficient
of `Xⁱ`. Let `x ∈ F_v ⊗[F] B` with `x τ_v(x) = 1` and `f` conjugate-reciprocal with
`f(x) = 0`, `f'(x)` a unit, and `1, x, …, x^{n-1}` linearly independent over
`F_v ⊗[F] E` (polynomials evaluated through `ψ`). Then there is an open set `U` of
coefficient coordinates (in the basis of `F_v ⊗[F] E` over `F_v` induced by `b`, for the
coefficients of `X⁰, …, X^{n-1}`) containing the coordinates of `f` such that every
conjugate-reciprocal `g` with coordinates in `U` has a root `y ∈ F_v ⊗[F] B` with
`y τ_v(y) = 1` and `1, y, …, y^{n-1}` linearly independent over `F_v ⊗[F] E`. -/
def NumberFieldUnitaryLocalRootNeighborhoodStatement : Prop :=
  ∀ (F E B : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    (τ : FirstKindInvolution F B),
    (∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e)) →
    ∀ (n : ℕ), Module.finrank E B = n ^ 2 →
    ∀ (z : E) (v : Global.Place F) (b : Module.Basis (Fin 2) F E)
      (x : Global.placeCompletion F v ⊗[F] B) (f : (Global.placeCompletion F v ⊗[F] E)[X]),
      x * τ.baseChange (Global.placeCompletion F v) x = 1 →
      f.Monic → f.natDegree = n →
      (∀ i ≤ n, f.coeff (n - i) =
        (-1) ^ n * ((1 : Global.placeCompletion F v) ⊗ₜ[F] z) *
          Algebra.TensorProduct.map
            (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
            (conjugation F E).toAlgHom (f.coeff i)) →
      f.eval₂ (Algebra.TensorProduct.map
          (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
          (IsScalarTower.toAlgHom F E B) :
            Global.placeCompletion F v ⊗[F] E →+* Global.placeCompletion F v ⊗[F] B) x = 0 →
      IsUnit ((derivative f).eval₂ (Algebra.TensorProduct.map
          (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
          (IsScalarTower.toAlgHom F E B) :
            Global.placeCompletion F v ⊗[F] E →+* Global.placeCompletion F v ⊗[F] B) x) →
      (∀ c : Fin n → Global.placeCompletion F v ⊗[F] E,
        ∑ i, Algebra.TensorProduct.map
            (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
            (IsScalarTower.toAlgHom F E B) (c i) * x ^ (i : ℕ) = 0 → c = 0) →
      ∃ U : Set (Fin n → Fin 2 → Global.placeCompletion F v),
        IsOpen U ∧
        (fun (i : Fin n) (j : Fin 2) =>
          (Algebra.TensorProduct.basis (Global.placeCompletion F v) b).repr (f.coeff i) j) ∈ U ∧
        ∀ g : (Global.placeCompletion F v ⊗[F] E)[X], g.Monic → g.natDegree = n →
          (∀ i ≤ n, g.coeff (n - i) =
            (-1) ^ n * ((1 : Global.placeCompletion F v) ⊗ₜ[F] z) *
              Algebra.TensorProduct.map
                (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
                (conjugation F E).toAlgHom (g.coeff i)) →
          (fun (i : Fin n) (j : Fin 2) =>
            (Algebra.TensorProduct.basis (Global.placeCompletion F v) b).repr (g.coeff i) j) ∈ U →
          ∃ y : Global.placeCompletion F v ⊗[F] B,
            y * τ.baseChange (Global.placeCompletion F v) y = 1 ∧
            g.eval₂ (Algebra.TensorProduct.map
                (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
                (IsScalarTower.toAlgHom F E B) :
                  Global.placeCompletion F v ⊗[F] E →+* Global.placeCompletion F v ⊗[F] B) y = 0 ∧
            ∀ c : Fin n → Global.placeCompletion F v ⊗[F] E,
              ∑ i, Algebra.TensorProduct.map
                  (AlgHom.id (Global.placeCompletion F v) (Global.placeCompletion F v))
                  (IsScalarTower.toAlgHom F E B) (c i) * y ^ (i : ℕ) = 0 → c = 0

end Langlands.CentralSimple
