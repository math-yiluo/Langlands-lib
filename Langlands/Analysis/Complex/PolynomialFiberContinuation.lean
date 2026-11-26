import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-! # Continuation of polynomial fibers -/

noncomputable section

open Filter Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis.PolynomialFiberContinuation

/-- If the spectral fibers of a family are polynomial on an open parameter subset, they are
polynomial of uniformly bounded degree throughout the connected parameter domain. -/
def PolynomialFiberContinuationStatement : Prop :=
  ∀ (U S : Set ℂ), IsOpen U → IsPreconnected U → IsOpen S → S.Nonempty → S ⊆ U →
  ∀ (σ : ℝ) (F : ℂ → ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → DifferentiableOn ℂ (fun z => F z s) U) →
    (∀ z ∈ S, ∃ P : Polynomial ℂ, ∀ s : ℂ, σ < s.re → F z s = P.eval s) →
    ∃ N : ℕ, ∀ z ∈ U, ∃ P : Polynomial ℂ, P.degree < N ∧
      ∀ s : ℂ, σ < s.re → F z s = P.eval s

theorem polynomialFiberContinuation : PolynomialFiberContinuationStatement := by
  classical
  intro U S hU hconn hS hSne hSU σ F hF hPoly
  let w (j : ℕ) : ℂ := ((σ + 1 + j : ℝ) : ℂ)
  have hw (j : ℕ) : σ < (w j).re := by
    change σ < ((σ + 1 + j : ℝ) : ℂ).re
    rw [Complex.ofReal_re, add_assoc, lt_add_iff_pos_right]
    positivity
  have hwinj : Function.Injective w := by
    intro i j hij
    have he := congrArg Complex.re hij
    simp only [w, Complex.ofReal_re, add_right_inj] at he
    exact_mod_cast he
  let p (N : ℕ) (z : ℂ) := Lagrange.interpolate (Finset.range N) w (fun j => F z (w j))
  have hp (N : ℕ) (s : ℂ) : DifferentiableOn ℂ (fun z => (p N z).eval s) U := by
    simp only [p, Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact DifferentiableOn.fun_sum fun j _ => (hF (w j) (hw j)).mul_const _
  let A (N : ℕ) : Set S := ⋂ s : {x : ℂ // σ < x.re}, {z | F z.val s.val = (p N z.val).eval s.val}
  have hAc (N : ℕ) : IsClosed (A N) := by
    apply isClosed_iInter
    intro s
    apply isClosed_eq
    · exact continuousOn_iff_continuous_domRestrict.mp ((hF s.val s.2).continuousOn.mono hSU)
    · exact continuousOn_iff_continuous_domRestrict.mp ((hp N s.val).continuousOn.mono hSU)
  have hCover : ⋃ N, A N = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨P, hP⟩ := hPoly z.val z.2
    let N := P.natDegree + 1
    have hN : P.degree < (Finset.range N).card := by
      rw [Finset.card_range]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self P.natDegree)
    have he : P = p N z.val :=
      Lagrange.eq_interpolate_of_eval_eq _ hwinj.injOn hN (fun j _ => (hP _ (hw j)).symm)
    exact mem_iUnion.mpr ⟨N, mem_iInter.mpr fun s => (hP _ s.2).trans (congrArg (Polynomial.eval s.val) he)⟩
  let : BaireSpace S := hS.baireSpace
  let : Nonempty S := hSne.to_subtype
  obtain ⟨N, b, hb⟩ := nonempty_interior_of_iUnion_of_closed hAc hCover
  have hnb : ((↑) : S → ℂ) '' interior (A N) ∈ 𝓝 (b : ℂ) :=
    (hS.isOpenMap_subtype_val _ isOpen_interior).mem_nhds ⟨b, hb, rfl⟩
  refine ⟨N, fun z hz => ⟨p N z, ?_, fun s hs => ?_⟩⟩
  · simpa only [Finset.card_range] using
      Lagrange.degree_interpolate_lt (fun j => F z (w j)) hwinj.injOn (s := Finset.range N)
  · have he : (fun x => F x s) =ᶠ[𝓝 (b : ℂ)] (fun x => (p N x).eval s) := by
      filter_upwards [hnb]
      rintro _ ⟨x, hx, rfl⟩
      exact mem_iInter.mp (interior_subset hx) ⟨s, hs⟩
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hF s hs).analyticOnNhd hU) ((hp N s).analyticOnNhd hU) hconn (hSU b.2) he hz

end Langlands.Analysis.PolynomialFiberContinuation
