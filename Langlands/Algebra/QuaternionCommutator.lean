import Langlands.Algebra.ReducedCharpolyDivision
import Langlands.Algebra.DivisionReducedCharpoly
import Langlands.Algebra.DivisionFieldEmbeddingsProof
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.NoncommRing

/-!
# Norm-one elements of quaternion division algebras as commutators

For a central division algebra `D` of reduced degree `2` over a field `K` (a quaternion
division algebra), let `z ∈ D` be a non-scalar element. Every element `a` of reduced norm `1`
is a commutator `a = y (z + s) y⁻¹ (z + s)⁻¹` for some scalar `s ∈ K` and unit `y ∈ Dˣ`.

The proof chooses `s` so that `a (z + s)` and `z + s` have the same reduced trace, hence the
same reduced characteristic polynomial, which is the minimal polynomial of `z + s`; the
Skolem–Noether theorem (`fieldEmbeddingsConjugate`) then conjugates `z + s` to `a (z + s)`.
On the way, the module introduces the reduced trace `reducedTrace` and the Cayley–Hamilton
identity `b² - Trd(b) b + Nrd(b) = 0` in reduced degree `2`.
-/

noncomputable section

universe u

open Polynomial Langlands.CentralSimple
open scoped TensorProduct

namespace Langlands.CentralDivision

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]

/-- The reduced trace: minus the subleading coefficient of the reduced characteristic
polynomial. -/
def reducedTrace (a : D) : K :=
  -(reducedCharpoly K D a).coeff (reducedDegree K D - 1)

/-- Under the chosen splitting chart, the reduced trace is the matrix trace. -/
theorem algebraMap_reducedTrace (a : D) :
    algebraMap K (finiteGaloisSplittingField K D) (reducedTrace K D a) =
      Matrix.trace (finiteGaloisSplittingChart K D (1 ⊗ₜ[K] a)) := by
  rw [reducedTrace, map_neg, ← Polynomial.coeff_map,
    reducedCharpoly_map_chart K D (finiteGaloisSplittingChart K D),
    Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]

theorem reducedTrace_add (a b : D) :
    reducedTrace K D (a + b) = reducedTrace K D a + reducedTrace K D b := by
  apply (algebraMap K (finiteGaloisSplittingField K D)).injective
  rw [map_add, algebraMap_reducedTrace, algebraMap_reducedTrace, algebraMap_reducedTrace,
    TensorProduct.tmul_add, map_add, Matrix.trace_add]

theorem reducedTrace_smul (t : K) (a : D) :
    reducedTrace K D (t • a) = t * reducedTrace K D a := by
  apply (algebraMap K (finiteGaloisSplittingField K D)).injective
  rw [map_mul, algebraMap_reducedTrace, algebraMap_reducedTrace, TensorProduct.tmul_smul,
    ← algebraMap_smul (finiteGaloisSplittingField K D) t, map_smul, Matrix.trace_smul,
    smul_eq_mul]

theorem reducedTrace_sub (a b : D) :
    reducedTrace K D (a - b) = reducedTrace K D a - reducedTrace K D b := by
  rw [eq_sub_iff_add_eq, ← reducedTrace_add, sub_add_cancel]

/-- In reduced degree `2` the reduced characteristic polynomial is
`X² - Trd(a) X + Nrd(a)`. -/
theorem reducedCharpoly_eq_quadratic (hd : reducedDegree K D = 2) (a : D) :
    reducedCharpoly K D a =
      X ^ 2 - C (reducedTrace K D a) * X + C (reducedNorm K D K (1 ⊗ₜ[K] a)) := by
  have hmon := reducedCharpoly_monic K D a
  have hdeg : (reducedCharpoly K D a).natDegree = 2 := by
    rw [reducedCharpoly_natDegree, hd]
  ext m
  rcases m with _ | _ | _ | m
  · rw [Langlands.CentralSimple.reducedCharpoly_coeff_zero_two K D hd]
    simp
  · simp [reducedTrace, hd]
  · have h2 := hmon.coeff_natDegree
    rw [hdeg] at h2
    rw [h2]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [coeff_X_pow]

/-- **Cayley–Hamilton** in reduced degree `2`: `a² - Trd(a) a + Nrd(a) = 0`. -/
theorem sq_sub_reducedTrace_add_reducedNorm (hd : reducedDegree K D = 2) (a : D) :
    a ^ 2 - algebraMap K D (reducedTrace K D a) * a +
      algebraMap K D (reducedNorm K D K (1 ⊗ₜ[K] a)) = 0 := by
  have h := aeval_reducedCharpoly K D a
  rw [reducedCharpoly_eq_quadratic K D hd] at h
  simpa [Algebra.smul_def] using h

theorem reducedTrace_one (hd : reducedDegree K D = 2) : reducedTrace K D 1 = 2 := by
  have h := sq_sub_reducedTrace_add_reducedNorm K D hd 1
  rw [← Algebra.TensorProduct.one_def, map_one, one_pow, mul_one, map_one] at h
  apply (algebraMap K D).injective
  have : algebraMap K D (reducedTrace K D 1) = 1 + 1 := by
    rw [← sub_eq_zero, ← neg_eq_zero, ← h]
    abel
  rw [this, one_add_one_eq_two, map_ofNat]

/-- **Norm-one elements are commutators.** Let `D` be a central division algebra of reduced
degree `2` and `z ∈ D` a non-scalar element. If `Nrd(a) = 1`, then there are `s ∈ K` and a
unit `y` with `a (z + s) = y (z + s) y⁻¹`. -/
theorem exists_mul_add_eq_conj (hd : reducedDegree K D = 2) {z : D}
    (hz : z ∉ Set.range (algebraMap K D)) {a : D}
    (ha : reducedNorm K D K (1 ⊗ₜ[K] a) = 1) :
    ∃ (s : K) (y : Dˣ), a * (z + algebraMap K D s) =
      (y : D) * (z + algebraMap K D s) * ((y⁻¹ : Dˣ) : D) := by
  by_cases ha1 : a = 1
  · refine ⟨0, 1, ?_⟩
    simp [ha1]
  have hT : reducedTrace K D (a - 1) ≠ 0 := by
    intro h0
    apply ha1
    have hCH := sq_sub_reducedTrace_add_reducedNorm K D hd a
    rw [reducedTrace_sub, reducedTrace_one K D hd, sub_eq_zero] at h0
    rw [h0, ha, map_one, map_ofNat] at hCH
    have : (a - 1) * (a - 1) = 0 := by
      rw [← hCH]
      noncomm_ring
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  obtain ⟨s, hs⟩ : ∃ s : K, s = -reducedTrace K D ((a - 1) * z) / reducedTrace K D (a - 1) :=
    ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : D, x = z + algebraMap K D s := ⟨_, rfl⟩
  have hxK : x ∉ Set.range (algebraMap K D) := by
    rintro ⟨k, hk⟩
    apply hz
    refine ⟨k - s, ?_⟩
    rw [map_sub, hk, hx, add_sub_cancel_right]
  have htr : reducedTrace K D (a * x) = reducedTrace K D x := by
    have h1 : a * x = x + (a - 1) * x := by noncomm_ring
    have h2 : (a - 1) * x = (a - 1) * z + s • (a - 1) := by
      rw [hx, mul_add, Algebra.smul_def, Algebra.commutes]
    rw [h1, reducedTrace_add, h2, reducedTrace_add, reducedTrace_smul, hs,
      div_mul_cancel₀ _ hT, add_neg_cancel, add_zero]
  have hnorm : reducedNorm K D K (1 ⊗ₜ[K] (a * x)) = reducedNorm K D K (1 ⊗ₜ[K] x) := by
    rw [show (1 : K) ⊗ₜ[K] (a * x) = ((1 : K) ⊗ₜ[K] a) * ((1 : K) ⊗ₜ[K] x) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, ha, one_mul]
  have hpoly : reducedCharpoly K D (a * x) = reducedCharpoly K D x := by
    rw [reducedCharpoly_eq_quadratic K D hd, reducedCharpoly_eq_quadratic K D hd, htr, hnorm]
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly K x = reducedCharpoly K D x := by
    have hle : (reducedCharpoly K D x).natDegree ≤ (minpoly K x).natDegree := by
      rw [reducedCharpoly_natDegree, hd]
      have h1 : (minpoly K x).natDegree ≠ 1 := fun h =>
        hxK (RingHom.mem_range.1 (minpoly.natDegree_eq_one_iff.1 h))
      have h0 : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hint
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (reducedCharpoly_monic K D x) (minpoly_dvd_reducedCharpoly K D x) hle).symm
  have : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hint⟩
  have : Module.Finite K (AdjoinRoot (minpoly K x)) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hint)).finite
  have hker : ∀ y : D, Polynomial.aeval y (minpoly K x) = 0 →
      ∀ p ∈ Ideal.span {minpoly K x}, Polynomial.aeval y p = 0 := by
    intro y hy p hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    rw [map_mul, hy, mul_zero]
  have hw : Polynomial.aeval (a * x) (minpoly K x) = 0 := by
    rw [hmin, ← hpoly]
    exact aeval_reducedCharpoly K D (a * x)
  let f1 : AdjoinRoot (minpoly K x) →ₐ[K] D :=
    Ideal.Quotient.liftₐ _ (Polynomial.aeval x) (hker x (minpoly.aeval K x))
  let f2 : AdjoinRoot (minpoly K x) →ₐ[K] D :=
    Ideal.Quotient.liftₐ _ (Polynomial.aeval (a * x)) (hker _ hw)
  obtain ⟨u, hu⟩ := fieldEmbeddingsConjugate K D (AdjoinRoot (minpoly K x)) f1 f2
  have h1 : f1 (AdjoinRoot.root (minpoly K x)) = x :=
    (Ideal.Quotient.lift_mk _ _ _).trans (Polynomial.aeval_X x)
  have h2 : f2 (AdjoinRoot.root (minpoly K x)) = a * x :=
    (Ideal.Quotient.lift_mk _ _ _).trans (Polynomial.aeval_X (a * x))
  have key := hu (AdjoinRoot.root (minpoly K x))
  rw [h1, h2] at key
  refine ⟨s, u⁻¹, ?_⟩
  rw [← hx, inv_inv]
  conv_rhs => rw [key]
  simp [mul_assoc]

end Langlands.CentralDivision
