import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Iterated Frobenius powers and coefficient maps

Over a field of exponential characteristic `p`, the power map `x ↦ x ^ p ^ e` is additive on every
commutative algebra. Two consequences: a coefficient map that agrees with the identity after
taking `p ^ e`-th powers on `A` still does so on `K ⊗[k] A`; and when `L / F` has exponent `e`
(every `ℓ ^ p ^ e` lies in `F`), the map `x ⊗ y ↦ 1 ⊗ x y` agrees with the identity on
`(L ⊗[F] L)[Λ]` after taking `p ^ e`-th powers.
-/

open scoped TensorProduct

namespace Langlands.GroupScheme.CocharacterDescent

/-- Over a field of exponential characteristic `p`, the power map `x ↦ x ^ p ^ e` of every
commutative algebra is additive. -/
theorem add_pow_expChar_pow_of_algebra (k : Type*) {R : Type*} [Field k] [CommRing R]
    [Algebra k R] (p : ℕ) [ExpChar k p] (e : ℕ) (x y : R) :
    (x + y) ^ p ^ e = x ^ p ^ e + y ^ p ^ e := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · have := expChar_of_injective_algebraMap (algebraMap k R).injective p
    exact add_pow_expChar_pow x y p e

/-- Agreement after taking `p ^ e`-th powers is preserved under sums. -/
theorem pow_eq_pow_map_add (k : Type*) {R : Type*} [Field k] [CommRing R] [Algebra k R]
    (p : ℕ) [ExpChar k p] (e : ℕ) (f : R →+ R) {x y : R} (hx : x ^ p ^ e = f x ^ p ^ e)
    (hy : y ^ p ^ e = f y ^ p ^ e) : (x + y) ^ p ^ e = f (x + y) ^ p ^ e := by
  rw [map_add, add_pow_expChar_pow_of_algebra k p e, add_pow_expChar_pow_of_algebra k p e, hx, hy]

/-- Agreement after taking `p ^ e`-th powers holds at `0`. -/
theorem pow_eq_pow_map_zero (k : Type*) {R : Type*} [Field k] [CommRing R] [Algebra k R]
    (p : ℕ) [ExpChar k p] (e : ℕ) (f : R →+ R) : (0 : R) ^ p ^ e = f 0 ^ p ^ e := by
  rw [map_zero]

/-- If an algebra map `g` of `A` agrees with the identity after taking `p ^ e`-th powers, so does
its base change `id ⊗ g` to `K ⊗[k] A`. -/
theorem pow_eq_pow_tensorProductMap {k K A : Type*} [Field k] [CommRing K] [Algebra k K]
    [CommRing A] [Algebra k A] (p : ℕ) [ExpChar k p] (e : ℕ) (g : A →ₐ[k] A)
    (hg : ∀ a, a ^ p ^ e = g a ^ p ^ e) (x : K ⊗[k] A) :
    x ^ p ^ e = Algebra.TensorProduct.map (AlgHom.id K K) g x ^ p ^ e := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow,
      Algebra.TensorProduct.tmul_pow, AlgHom.id_apply, hg]
  | add x y hx hy =>
    exact pow_eq_pow_map_add k p e (Algebra.TensorProduct.map (AlgHom.id K K) g).toAddMonoidHom hx hy

/-- If every `p ^ e`-th power of `L` lies in `F`, then `x ↦ 1 ⊗ (multiplication of x)` agrees with
the identity on `L ⊗[F] L` after taking `p ^ e`-th powers. -/
theorem pow_eq_pow_includeRight_lmul' {F L : Type*} [Field F] [CommRing L] [Algebra F L]
    (p : ℕ) [ExpChar F p] (e : ℕ) (hL : ∀ ℓ : L, ℓ ^ p ^ e ∈ Set.range (algebraMap F L))
    (r : L ⊗[F] L) :
    r ^ p ^ e =
      ((Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).comp
        (Algebra.TensorProduct.lmul' F)) r ^ p ^ e := by
  induction r using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨c, hc⟩ := hL x
    rw [AlgHom.comp_apply, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow,
      Algebra.TensorProduct.tmul_pow, one_pow, mul_pow, ← hc, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
  | add x y hx hy =>
    exact pow_eq_pow_map_add F p e
      ((Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).comp
        (Algebra.TensorProduct.lmul' F)).toAddMonoidHom hx hy

/-- A coefficient map of a group algebra agrees with the identity after taking `p ^ e`-th powers
as soon as it does so on coefficients. -/
theorem pow_eq_pow_mapAlgHom {k R Λ : Type*} [Field k] [CommRing R] [Algebra k R]
    [AddCommMonoid Λ] (p : ℕ) [ExpChar k p] (e : ℕ) (f : R →ₐ[k] R)
    (hf : ∀ r, r ^ p ^ e = f r ^ p ^ e) (a : AddMonoidAlgebra R Λ) :
    a ^ p ^ e = AddMonoidAlgebra.mapAlgHom Λ f a ^ p ^ e := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => exact pow_eq_pow_map_zero k p e (AddMonoidAlgebra.mapAlgHom Λ f).toAddMonoidHom
  | add x y hx hy =>
    exact pow_eq_pow_map_add k p e (AddMonoidAlgebra.mapAlgHom Λ f).toAddMonoidHom hx hy
  | single γ r =>
    rw [AddMonoidAlgebra.mapAlgHom_single, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_pow, hf]

/-- **Frobenius identity for purely inseparable descent.** If every `p ^ e`-th power of `L` lies
in `F`, then the coefficient map of `(L ⊗[F] L)[Λ]` induced by `x ⊗ y ↦ 1 ⊗ x y` agrees with the
identity after taking `p ^ e`-th powers. -/
theorem pow_eq_pow_mapAlgHom_includeRight_lmul' {F L Λ : Type*} [Field F] [CommRing L]
    [Algebra F L] [AddCommMonoid Λ] (p : ℕ) [ExpChar F p] (e : ℕ)
    (hL : ∀ ℓ : L, ℓ ^ p ^ e ∈ Set.range (algebraMap F L)) (a : AddMonoidAlgebra (L ⊗[F] L) Λ) :
    a ^ p ^ e =
      AddMonoidAlgebra.mapAlgHom Λ ((Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).comp
        (Algebra.TensorProduct.lmul' F)) a ^ p ^ e :=
  pow_eq_pow_mapAlgHom p e _ (pow_eq_pow_includeRight_lmul' p e hL) a

end Langlands.GroupScheme.CocharacterDescent
