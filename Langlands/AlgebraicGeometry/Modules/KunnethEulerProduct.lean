import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Finiteness.Basic

/-! # Euler characteristics of Künneth-type cohomology -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type u} [Field K]

/-- The index set `{(a, b) | a + b = n}` of a Künneth decomposition, as a finite type. -/
abbrev kunnethIndexFintype (n : ℕ) : Fintype {ab : ℕ × ℕ // ab.1 + ab.2 = n} :=
  Fintype.subtype (Finset.antidiagonal n) (fun _ => Finset.mem_antidiagonal)

/-- The Künneth direct sum of two families of finite-dimensional spaces. -/
abbrev kunnethSum (A B : ℕ → ModuleCat.{u} K) (n : ℕ) : ModuleCat.{u} K :=
  ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
    TensorProduct K (A ab.1.1) (B ab.1.2))

/-- The dimension of a Künneth direct sum is the antidiagonal sum of products of dimensions. -/
theorem finrank_kunnethSum (A B : ℕ → ModuleCat.{u} K)
    (hA : ∀ a, Module.Finite K (A a)) (hB : ∀ b, Module.Finite K (B b)) (n : ℕ) :
    Module.finrank K (kunnethSum A B n) =
      ∑ ab ∈ Finset.antidiagonal n,
        Module.finrank K (A ab.1) * Module.finrank K (B ab.2) := by
  let := kunnethIndexFintype n
  have hfin : ∀ ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n},
      Module.Finite K (TensorProduct K (A ab.1.1) (B ab.1.2)) := fun ab => by
    have := hA ab.1.1
    have := hB ab.1.2
    infer_instance
  rw [Module.finrank_directSum (R := K)
    (fun ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n} => TensorProduct K (A ab.1.1) (B ab.1.2))]
  rw [Finset.sum_subtype (Finset.antidiagonal n) (fun ab => Finset.mem_antidiagonal)
    (fun ab : ℕ × ℕ => Module.finrank K (A ab.1) * Module.finrank K (B ab.2))]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact Module.finrank_tensorProduct

/-- A finite-dimensional module of dimension zero is a zero object. -/
theorem isZero_of_finrank_eq_zero (V : ModuleCat.{u} K) [Module.Finite K V]
    (h : Module.finrank K V = 0) : IsZero V := by
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  exact ModuleCat.isZero_of_subsingleton V

/-- The truncated alternating polynomial `∑_{a < N} (-1)^a dim A_a X^a`. -/
def alternatingDimensionPolynomial (A : ℕ → ModuleCat.{u} K) (N : ℕ) : ℤ[X] :=
  ∑ a ∈ Finset.range N, C ((-1 : ℤ) ^ a * (Module.finrank K (A a) : ℤ)) * X ^ a

theorem coeff_alternatingDimensionPolynomial (A : ℕ → ModuleCat.{u} K) (N : ℕ)
    (hN : ∀ a, N ≤ a → Module.finrank K (A a) = 0) (a : ℕ) :
    (alternatingDimensionPolynomial A N).coeff a =
      (-1 : ℤ) ^ a * (Module.finrank K (A a) : ℤ) := by
  unfold alternatingDimensionPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range N) a]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    simp [hN a h]

theorem natDegree_alternatingDimensionPolynomial_le (A : ℕ → ModuleCat.{u} K) (N : ℕ) :
    (alternatingDimensionPolynomial A N).natDegree ≤ N := by
  unfold alternatingDimensionPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  exact (Finset.mem_range.mp ha).le

theorem eval_one_alternatingDimensionPolynomial (A : ℕ → ModuleCat.{u} K) (N : ℕ) :
    (alternatingDimensionPolynomial A N).eval 1 =
      ∑ a ∈ Finset.range N, (-1 : ℤ) ^ a * (Module.finrank K (A a) : ℤ) := by
  unfold alternatingDimensionPolynomial
  rw [Polynomial.eval_finsetSum]
  simp

/-- If the `n`-th cohomology of `Q` is the Künneth sum of the cohomologies of `L` and `M`
in every degree, then `Q` has finite cohomology. -/
theorem hasFiniteCohomology_of_kunnethIso
    {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) (fZ : Z ⟶ Spec (CommRingCat.of K))
    (L : X.Modules) (M : Y.Modules) (Q : Z.Modules)
    (hL : HasFiniteCohomology fX L) (hM : HasFiniteCohomology fY M)
    (e : ∀ n : ℕ, (relativeCohomology fZ n).obj Q ≅
      kunnethSum (fun a => (relativeCohomology fX a).obj L)
        (fun b => (relativeCohomology fY b).obj M) n) :
    HasFiniteCohomology fZ Q := by
  obtain ⟨NL, hNL⟩ := hL.2
  obtain ⟨NM, hNM⟩ := hM.2
  have hfin : ∀ n, Module.Finite K ((relativeCohomology fZ n).obj Q) := fun n => by
    letI := kunnethIndexFintype n
    have : ∀ ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n},
        Module.Finite K (TensorProduct K ((relativeCohomology fX ab.1.1).obj L)
          ((relativeCohomology fY ab.1.2).obj M)) := fun ab => by
      have := hL.1 ab.1.1
      have := hM.1 ab.1.2
      infer_instance
    have hpi : Module.Finite K (∀ ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n},
        TensorProduct K ((relativeCohomology fX ab.1.1).obj L)
          ((relativeCohomology fY ab.1.2).obj M)) := Module.Finite.pi
    exact Module.Finite.equiv ((DirectSum.linearEquivFunOnFintype K _ (fun ab :
        {ab : ℕ × ℕ // ab.1 + ab.2 = n} => TensorProduct K
          ((relativeCohomology fX ab.1.1).obj L) ((relativeCohomology fY ab.1.2).obj M))).symm.trans
      (e n).symm.toLinearEquiv)
  refine ⟨hfin, NL + NM, fun n hn => ?_⟩
  have := hfin n
  apply isZero_of_finrank_eq_zero
  rw [(e n).toLinearEquiv.finrank_eq, finrank_kunnethSum _ _ hL.1 hM.1]
  refine Finset.sum_eq_zero fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  by_cases ha : NL ≤ ab.1
  · have := hL.1 ab.1
    have : Subsingleton ((relativeCohomology fX ab.1).obj L) :=
      ModuleCat.subsingleton_of_isZero (hNL ab.1 ha)
    simp [Module.finrank_zero_of_subsingleton]
  · have hb : NM ≤ ab.2 := by omega
    have : Subsingleton ((relativeCohomology fY ab.2).obj M) :=
      ModuleCat.subsingleton_of_isZero (hNM ab.2 hb)
    simp [Module.finrank_zero_of_subsingleton]

/-- If the `n`-th cohomology of `Q` is the Künneth sum of the cohomologies of `L` and `M`
in every degree, then `χ(Q) = χ(L) χ(M)`. -/
theorem eulerCharacteristic_eq_mul_of_kunnethIso
    {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) (fZ : Z ⟶ Spec (CommRingCat.of K))
    (L : X.Modules) (M : Y.Modules) (Q : Z.Modules)
    (hL : HasFiniteCohomology fX L) (hM : HasFiniteCohomology fY M)
    (hQ : HasFiniteCohomology fZ Q)
    (e : ∀ n : ℕ, (relativeCohomology fZ n).obj Q ≅
      kunnethSum (fun a => (relativeCohomology fX a).obj L)
        (fun b => (relativeCohomology fY b).obj M) n) :
    eulerCharacteristic fZ Q hQ = eulerCharacteristic fX L hL * eulerCharacteristic fY M hM := by
  obtain ⟨NL, hNL⟩ := hL.2
  obtain ⟨NM, hNM⟩ := hM.2
  obtain ⟨NQ, hNQ⟩ := hQ.2
  let A : ℕ → ModuleCat.{u} K := fun a => (relativeCohomology fX a).obj L
  let B : ℕ → ModuleCat.{u} K := fun b => (relativeCohomology fY b).obj M
  have hA : ∀ a, NL ≤ a → Module.finrank K (A a) = 0 := fun a ha => by
    have : Subsingleton (A a) := ModuleCat.subsingleton_of_isZero (hNL a ha)
    exact Module.finrank_zero_of_subsingleton
  have hB : ∀ b, NM ≤ b → Module.finrank K (B b) = 0 := fun b hb => by
    have : Subsingleton (B b) := ModuleCat.subsingleton_of_isZero (hNM b hb)
    exact Module.finrank_zero_of_subsingleton
  let P := alternatingDimensionPolynomial A NL
  let R := alternatingDimensionPolynomial B NM
  have hcoeff : ∀ n, (P * R).coeff n = (-1 : ℤ) ^ n *
      (Module.finrank K ((relativeCohomology fZ n).obj Q) : ℤ) := fun n => by
    rw [Polynomial.coeff_mul, (e n).toLinearEquiv.finrank_eq,
      finrank_kunnethSum _ _ hL.1 hM.1, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    rw [coeff_alternatingDimensionPolynomial A NL hA,
      coeff_alternatingDimensionPolynomial B NM hB, ← hab, pow_add]
    push_cast
    ring
  have hdeg : (P * R).natDegree < NL + NM + 1 :=
    lt_of_le_of_lt ((Polynomial.natDegree_mul_le).trans (add_le_add
      (natDegree_alternatingDimensionPolynomial_le A NL)
      (natDegree_alternatingDimensionPolynomial_le B NM))) (Nat.lt_succ_self _)
  have hQsum := eulerCharacteristic_eq_sum_range fZ Q hQ (max NQ (NL + NM + 1))
    (fun n hn => hNQ n (le_of_max_le_left hn))
  have hLsum := eulerCharacteristic_eq_sum_range fX L hL NL hNL
  have hMsum := eulerCharacteristic_eq_sum_range fY M hM NM hNM
  rw [hQsum, hLsum, hMsum, ← eval_one_alternatingDimensionPolynomial A NL,
    ← eval_one_alternatingDimensionPolynomial B NM, ← Polynomial.eval_mul,
    Polynomial.eval_eq_sum_range' (lt_of_lt_of_le hdeg (le_max_right _ _))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hcoeff n, one_pow, mul_one]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
