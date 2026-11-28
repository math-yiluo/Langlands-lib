import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.RingTheory.TensorProduct.Free

/-! # A place forcing irreducibility of conjugate-reciprocal polynomials -/

universe u

open scoped TensorProduct
open Polynomial

namespace Langlands.Global

open Langlands.GroupScheme.SU3Root

/-- **A place forcing irreducibility of conjugate-reciprocal polynomials.**
Let `E/F` be a separable quadratic extension of a number field with nontrivial automorphism
`e ↦ ē`, let `z ∈ E` with `z z̄ = 1`, let `n > 0` and fix an `F`-basis `b` of `E`. Call a
monic polynomial `g` of degree `n` *conjugate-reciprocal* (for `z`) when
`g_{n-i} = (-1)ⁿ z ḡ_i` for `0 ≤ i ≤ n`, where `g_i` is the coefficient of `Xⁱ`. Outside
every finite set of places of `F` there is a place `v`, a conjugate-reciprocal monic
polynomial `f` of degree `n` over `F_v ⊗[F] E`, and an open set `U` of coefficient
coordinates (in the basis of `F_v ⊗[F] E` over `F_v` induced by `b`, for the coefficients of
`X⁰, …, X^{n-1}`) containing the coordinates of `f`, such that every conjugate-reciprocal
monic polynomial of degree `n` over `E` whose coefficient coordinates at `v` lie in `U` is
irreducible over `E`. -/
def ConjugateReciprocalIrreduciblePlaceStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (z : E), z * conjugation F E z = 1 →
    ∀ (n : ℕ), 0 < n → ∀ (b : Module.Basis (Fin 2) F E) (S : Finset (Place F)),
      ∃ v : Place F, v ∉ S ∧
        ∃ (f : (placeCompletion F v ⊗[F] E)[X]) (U : Set (Fin n → Fin 2 → placeCompletion F v)),
          f.Monic ∧ f.natDegree = n ∧
          (∀ i ≤ n, f.coeff (n - i) =
            (-1) ^ n * ((1 : placeCompletion F v) ⊗ₜ[F] z) *
              Algebra.TensorProduct.map (AlgHom.id (placeCompletion F v) (placeCompletion F v))
                (conjugation F E).toAlgHom (f.coeff i)) ∧
          IsOpen U ∧
          (fun (i : Fin n) (j : Fin 2) => (Algebra.TensorProduct.basis (placeCompletion F v) b).repr
            (f.coeff i) j) ∈ U ∧
          ∀ g : E[X], g.Monic → g.natDegree = n →
            (∀ i ≤ n, g.coeff (n - i) = (-1) ^ n * z * conjugation F E (g.coeff i)) →
            (fun (i : Fin n) (j : Fin 2) => (Algebra.TensorProduct.basis (placeCompletion F v) b).repr
              ((1 : placeCompletion F v) ⊗ₜ[F] g.coeff i) j) ∈ U →
            Irreducible g

end Langlands.Global
