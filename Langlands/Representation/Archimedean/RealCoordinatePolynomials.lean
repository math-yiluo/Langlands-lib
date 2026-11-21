import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Polynomial functions in real linear coordinates -/

noncomputable section

universe u v

open scoped ContDiff

set_option autoImplicit false

namespace Langlands.Archimedean

/-- Complex-valued polynomials formed from real linear coordinates. -/
def realCoordinatePolynomials (A : Type u) [AddCommGroup A] [Module ℝ A] : Subalgebra ℂ (A → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun l : A →ₗ[ℝ] ℝ => fun a => (l a : ℂ))

section Basic

variable {A : Type u} [AddCommGroup A] [Module ℝ A]

lemma realLinear_mem_realCoordinatePolynomials (l : A →ₗ[ℝ] ℝ) :
    (fun a => (l a : ℂ)) ∈ realCoordinatePolynomials A :=
  Algebra.subset_adjoin ⟨l, rfl⟩

lemma star_mem_realCoordinatePolynomials {p : A → ℂ} (hp : p ∈ realCoordinatePolynomials A) :
    star p ∈ realCoordinatePolynomials A := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨l, rfl⟩ := hp
    convert realLinear_mem_realCoordinatePolynomials l using 1
    ext a
    simp
  | algebraMap c =>
    convert (realCoordinatePolynomials A).algebraMap_mem (star c) using 1
    funext a
    rfl
  | add p q _ _ hp hq => rw [star_add]; exact (realCoordinatePolynomials A).add_mem hp hq
  | mul p q _ _ hp hq => rw [star_mul]; exact (realCoordinatePolynomials A).mul_mem hq hp

end Basic

section Smooth

variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

/-- Real coordinate polynomials are smooth on their whole real vector space. -/
theorem contDiff_of_mem_realCoordinatePolynomials {p : A → ℂ}
    (hp : p ∈ realCoordinatePolynomials A) : ContDiff ℝ ∞ p := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨l, rfl⟩ := hp
    exact Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.mk l l.continuous_of_finiteDimensional).contDiff
  | algebraMap c => exact contDiff_const
  | add p q _ _ hp hq => exact hp.add hq
  | mul p q _ _ hp hq => exact hp.mul hq

end Smooth

section Products

variable {A : Type u} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

/-- A polynomial of a product has a finite separated expansion into
polynomials of the two factors. -/
theorem exists_realCoordinatePolynomials_product_expansion {p : A → ℂ}
    (hp : p ∈ realCoordinatePolynomials A) :
    ∃ (I : Type) (_ : Fintype I) (f g : I → A → ℂ),
      (∀ i, f i ∈ realCoordinatePolynomials A) ∧ (∀ i, g i ∈ realCoordinatePolynomials A) ∧
        ∀ a b, p (a * b) = ∑ i, f i a * g i b := by
  classical
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨l, rfl⟩ := hp
    let e := Module.finBasis ℝ A
    let L (i : Fin (Module.finrank ℝ A)) := l.comp (LinearMap.mul ℝ A (e i))
    refine ⟨_, inferInstance, fun i a => (e.coord i a : ℂ), fun i b => (L i b : ℂ),
      fun i => realLinear_mem_realCoordinatePolynomials (e.coord i),
      fun i => realLinear_mem_realCoordinatePolynomials (L i), fun a b => ?_⟩
    have he := congrArg (fun x : A => l (x * b)) (e.sum_repr a)
    simp only [Finset.sum_mul, Algebra.smul_mul_assoc, map_sum, map_smul, smul_eq_mul] at he
    change ((l (a * b) : ℝ) : ℂ) = ∑ i, (e.repr a i : ℂ) * (l (e i * b) : ℂ)
    exact_mod_cast he.symm
  | algebraMap z =>
    refine ⟨Unit, inferInstance, fun _ => algebraMap ℂ (A → ℂ) z, fun _ => 1,
      fun _ => (realCoordinatePolynomials A).algebraMap_mem z,
      fun _ => (realCoordinatePolynomials A).one_mem, fun a b => ?_⟩
    simp
  | add p q _ _ hp hq =>
    obtain ⟨I, _, f, g, hf, hg, hp⟩ := hp
    obtain ⟨J, _, f', g', hf', hg', hq⟩ := hq
    refine ⟨I ⊕ J, inferInstance, Sum.elim f f', Sum.elim g g', ?_, ?_, fun a b => ?_⟩
    · rintro (i | j)
      · exact hf i
      · exact hf' j
    · rintro (i | j)
      · exact hg i
      · exact hg' j
    · simp only [Pi.add_apply, hp, hq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  | mul p q _ _ hp hq =>
    obtain ⟨I, _, f, g, hf, hg, hp⟩ := hp
    obtain ⟨J, _, f', g', hf', hg', hq⟩ := hq
    refine ⟨I × J, inferInstance, fun ij => f ij.1 * f' ij.2, fun ij => g ij.1 * g' ij.2,
      fun ij => (realCoordinatePolynomials A).mul_mem (hf ij.1) (hf' ij.2),
      fun ij => (realCoordinatePolynomials A).mul_mem (hg ij.1) (hg' ij.2), fun a b => ?_⟩
    rw [Pi.mul_apply, hp, hq, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_mul_mul_comm _ _ _ _

/-- Multiples of a fixed vector by a coordinate polynomial have a
finite-dimensional space of right translates. -/
theorem finiteDimensional_span_rightTranslate_smul_polynomial
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {p : A → ℂ} (hp : p ∈ realCoordinatePolynomials A) (v : V) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun b : A => fun a : A => p (a * b) • v)) := by
  classical
  obtain ⟨I, _, f, g, _, _, h⟩ := exists_realCoordinatePolynomials_product_expansion hp
  let U := Submodule.span ℂ (Set.range fun i : I => fun a => f i a • v)
  have : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  apply Submodule.finiteDimensional_of_le (S₂ := U)
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  have he : (fun a => p (a * b) • v) = ∑ i, g i b • (fun a => f i a • v) := by
    funext a
    rw [h, Finset.sum_smul, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_smul, mul_comm]
  change (fun a => p (a * b) • v) ∈ U
  rw [he]
  exact U.sum_mem fun i _ => U.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

end Products

end Langlands.Archimedean
