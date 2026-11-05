import Langlands.Algebra.FiniteHopfCharZero
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

/-! # Uniform convolution exponents of finite commutative Hopf algebras -/

noncomputable section

open Coalgebra TensorProduct WithConv

namespace Langlands.FiniteHopfUniformExponent

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Forgetting multiplicativity respects convolution. -/
def linearize {A : Type*} [CommRing A] [Algebra k A] :
    WithConv (H →ₐ[k] A) →* WithConv (H →ₗ[k] A) where
  toFun f := toConv f.ofConv.toLinearMap
  map_one' := AlgHom.toLinearMap_convOne
  map_mul' := AlgHom.toLinearMap_convMul

theorem linearize_injective {A : Type*} [CommRing A] [Algebra k A] :
    Function.Injective (linearize (k := k) (H := H) (A := A)) := by
  intro f g h
  exact WithConv.ext (AlgHom.toLinearMap_injective (WithConv.toConv_injective h))

/-- Convolution multiplies ideals of values. -/
theorem conv_mem_mul {A : Type*} [CommRing A] [Algebra k A]
    {f g : WithConv (H →ₗ[k] A)} {I J : Ideal A}
    (hf : ∀ b, f b ∈ I) (hg : ∀ b, g b ∈ J) (b : H) : (f * g) b ∈ I * J := by
  rw [(ℛ k b).convMul_apply]
  exact sum_mem fun i _ => Ideal.mul_mem_mul (hf _) (hg _)

/-- Convolution powers of an ideal-valued map take values in the corresponding ideal powers. -/
theorem convPow_mem_pow {A : Type*} [CommRing A] [Algebra k A]
    {f : WithConv (H →ₗ[k] A)} {I : Ideal A} (hf : ∀ b, f b ∈ I)
    (n : ℕ) (b : H) : (f ^ n) b ∈ I ^ n := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact conv_mem_mul (fun b => ih b) hf b

/-- Nilpotence of an ideal of values implies convolution nilpotence. -/
theorem isNilpotent_of_values {A : Type*} [CommRing A] [Algebra k A]
    {f : WithConv (H →ₗ[k] A)} {I : Ideal A} (hI : IsNilpotent I)
    (hf : ∀ b, f b ∈ I) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply WithConv.ext
  apply LinearMap.ext
  intro b
  have hb := convPow_mem_pow hf n b
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hb
  exact hb

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

/-- The product of all residue-field images of a coordinate-valued point. -/
def residueImages : WithConv (H →ₐ[k] H) →*
    (∀ m : MaximalSpectrum H, WithConv (H →ₐ[k] H ⧸ m.asIdeal)) where
  toFun f m := Langlands.FiniteHopfConvolutionPower.postcomp (Ideal.Quotient.mkₐ k m.asIdeal) f
  map_one' := by
    funext m
    exact map_one (Langlands.FiniteHopfConvolutionPower.postcomp (Ideal.Quotient.mkₐ k m.asIdeal))
  map_mul' f g := by
    funext m
    exact map_mul (Langlands.FiniteHopfConvolutionPower.postcomp (Ideal.Quotient.mkₐ k m.asIdeal)) f g

/-- A single positive power of the universal point becomes the identity in every residue field. -/
theorem exists_residueImages_pow_eq_one [Module.Finite k H] :
    ∃ n : ℕ, 0 < n ∧ residueImages (toConv (AlgHom.id k H)) ^ n = 1 := by
  let : IsArtinianRing H := IsArtinianRing.of_finite k H
  have (m : MaximalSpectrum H) : Field (H ⧸ m.asIdeal) :=
    IsArtinianRing.fieldOfSubtypeIsMaximal H m
  have (m : MaximalSpectrum H) : Finite (WithConv (H →ₐ[k] H ⧸ m.asIdeal)) :=
    @Finite.of_equiv _ _ (Finite.algHom k H (H ⧸ m.asIdeal)) (WithConv.equiv _).symm
  have : Finite (∀ m : MaximalSpectrum H, WithConv (H →ₐ[k] H ⧸ m.asIdeal))ˣ :=
    Finite.of_injective _ Units.val_injective
  have hunit : IsUnit (residueImages (toConv (AlgHom.id k H))) :=
    (Group.isUnit (toConv (AlgHom.id k H))).map residueImages
  exact hunit.isOfFinOrder.exists_pow_eq_one

/-- The difference of a positive convolution power of the universal point from one has
values in the nilradical. -/
theorem exists_pow_sub_one_values_nilradical [Module.Finite k H] :
    ∃ n : ℕ, 0 < n ∧ ∀ b : H,
      ((linearize (toConv (AlgHom.id k H))) ^ n - 1) b ∈ nilradical H := by
  let : IsArtinianRing H := IsArtinianRing.of_finite k H
  obtain ⟨n, hn, hpow⟩ := exists_residueImages_pow_eq_one (k := k) (H := H)
  refine ⟨n, hn, fun b => ?_⟩
  rw [IsArtinianRing.nilradical_eq_iInf, Ideal.mem_iInf]
  intro m
  have hm := congrArg (fun f => f m b) hpow
  rw [← map_pow] at hm
  change (Ideal.Quotient.mkₐ k m.asIdeal)
    (((toConv (AlgHom.id k H) : WithConv (H →ₐ[k] H)) ^ n) b) =
      (Ideal.Quotient.mkₐ k m.asIdeal) (algebraMap k H (counit b)) at hm
  rw [← map_pow]
  change _ ∈ m.asIdeal
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change (Ideal.Quotient.mkₐ k m.asIdeal) (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  exact hm

/-- If the coordinate algebra is reduced, the universal point has finite order. -/
theorem exists_pow_eq_one_of_isReduced [Module.Finite k H] [IsReduced H] :
    ∃ n : ℕ, 0 < n ∧ (toConv (AlgHom.id k H) : WithConv (H →ₐ[k] H)) ^ n = 1 := by
  obtain ⟨n, hn, hv⟩ := exists_pow_sub_one_values_nilradical (k := k) (H := H)
  refine ⟨n, hn, linearize_injective ?_⟩
  rw [map_pow, map_one, ← sub_eq_zero]
  apply WithConv.ext
  apply LinearMap.ext
  intro b
  change _ = (0 : H)
  simpa only [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] using hv b

/-- In positive characteristic, a nilpotent difference from one is killed by a prime power.
The ambient algebra need not be commutative or nontrivial. -/
theorem exists_prime_pow_eq_one_of_sub_isNilpotent
    {A : Type*} [Ring A] [Algebra k A] (p : ℕ) [Fact p.Prime] [CharP k p]
    {x : A} (hx : IsNilpotent (x - 1)) : ∃ r : ℕ, x ^ (p ^ r) = 1 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  let : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  have hzero := pow_eq_zero_of_le
    (Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt) : r ≤ p ^ r) hr
  rwa [sub_pow_char_pow_of_commute p r (Commute.one_right x), one_pow, sub_eq_zero] at hzero

/-- A finite-dimensional commutative Hopf algebra in positive characteristic has a
positive convolution exponent, without a cocommutativity hypothesis. -/
theorem exists_pow_eq_one_of_charP [Module.Finite k H]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ n : ℕ, 0 < n ∧ (toConv (AlgHom.id k H) : WithConv (H →ₐ[k] H)) ^ n = 1 := by
  let : IsArtinianRing H := IsArtinianRing.of_finite k H
  obtain ⟨n, hn, hv⟩ := exists_pow_sub_one_values_nilradical (k := k) (H := H)
  have hnil : IsNilpotent ((linearize (toConv (AlgHom.id k H))) ^ n - 1) :=
    isNilpotent_of_values IsArtinianRing.isNilpotent_nilradical hv
  obtain ⟨r, hr⟩ := exists_prime_pow_eq_one_of_sub_isNilpotent (k := k) p hnil
  refine ⟨n * p ^ r, Nat.mul_pos hn (pow_pos (Fact.out : p.Prime).pos r),
    linearize_injective ?_⟩
  rw [map_pow, map_one, pow_mul]
  exact hr

/-- Every finite-dimensional commutative Hopf algebra over a field has a positive
convolution exponent for its universal point. -/
theorem exists_pow_eq_one [Module.Finite k H] :
    ∃ n : ℕ, 0 < n ∧ (toConv (AlgHom.id k H) : WithConv (H →ₐ[k] H)) ^ n = 1 := by
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let : CharZero k := hzero
    let : IsReduced H := Langlands.FiniteHopfCharZero.isReduced (k := k)
    exact exists_pow_eq_one_of_isReduced
  · let : Fact p.Prime := hp
    let : CharP k p := hchar
    exact exists_pow_eq_one_of_charP p

end Langlands.FiniteHopfUniformExponent
