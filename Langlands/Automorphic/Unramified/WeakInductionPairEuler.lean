import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Representation.Unramified.WeakTransfer

/-! # The unramified Rankin–Selberg projection formula for weak induction -/

noncomputable section

universe uF uE

set_option autoImplicit false

open scoped NumberField

namespace Langlands.Automorphic.Unramified

open Filter Polynomial
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Global.CuspidalPairFunctionalEquation

private theorem comp_prod {ι : Type*} (s : Finset ι) (P : ι → ℂ[X]) (Q : ℂ[X]) :
    (∏ i ∈ s, P i).comp Q = ∏ i ∈ s, (P i).comp Q :=
  map_prod (Polynomial.compRingHom Q) P s

private theorem pairEulerPolynomial_eq_prod_comp {n k : ℕ} (a : Eigenvalues n)
    (b : Fin k → ℂˣ) :
    pairEulerPolynomial a (Eigenvalues.ofTuple b) =
      ∏ j, a.eulerPolynomial.comp (C (b j : ℂ) * X) := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n a
  rw [pairEulerPolynomial_ofTuple, Eigenvalues.eulerPolynomial_ofTuple, Finset.prod_comm]
  simp only [comp_prod, sub_comp, one_comp, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]

/-- Substitution in the first member of a pair gives the projection formula:
at the `i`th place, base change of the second spectrum takes `f i`th powers. -/
theorem pairEulerPolynomial_of_inducedEulerPolynomial {ι : Type*} [Fintype ι]
    {n m k : ℕ} (a : Eigenvalues n) (t : ι → Eigenvalues m) (b : Eigenvalues k) (f : ι → ℕ)
    (h : a.eulerPolynomial = ∏ i, (t i).eulerPolynomial.comp (X ^ f i)) :
    pairEulerPolynomial a b =
      ∏ i, (pairEulerPolynomial (t i) (b.power (f i))).comp (X ^ f i) := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective k b
  simp_rw [Eigenvalues.power_ofTuple, pairEulerPolynomial_eq_prod_comp, h, comp_prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Polynomial.comp_assoc, Polynomial.comp_assoc]
  have hpow : ((z j ^ f i : ℂˣ) : ℂ) = (z j : ℂ) ^ f i :=
    map_pow (Units.coeHom ℂ) (z j) (f i)
  simp only [pow_comp, mul_comp, C_comp, X_comp, mul_pow, ← C_pow, hpow]

/-- The pair of a weak induction with a second downstairs spectrum has the
Euler product of the upper pair with weak base change, at almost every place. -/
def WeakInductionPairEulerStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n m k : ℕ)
    (s : SpectralSystem (FinitePlace F) n) (t : SpectralSystem (FinitePlace E) m)
    (b : SpectralSystem (FinitePlace F) k) (b' : SpectralSystem (FinitePlace E) k),
    s.IsArithmeticWeakInductionOf t →
    b'.IsArithmeticWeakBaseChangeOf b →
    ∀ᶠ v in cofinite,
      ∃ (hs : v ∉ s.exceptional) (hb : v ∉ b.exceptional)
        (ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ t.exceptional)
        (hb' : ∀ w : FinitePlacesAbove E v, w.1 ∉ b'.exceptional),
        pairEulerPolynomial (s.eigenvalues v hs) (b.eigenvalues v hb) =
          ∏ w : FinitePlacesAbove E v,
            (pairEulerPolynomial (t.eigenvalues w.1 (ht w)) (b'.eigenvalues w.1 (hb' w))).comp
              (X ^ w.1.asIdeal.inertiaDeg (𝓞 F))

theorem weakInductionPairEuler : WeakInductionPairEulerStatement.{uF, uE} := by
  intro F E _ _ _ _ _ n m k s t b b' hst hbb'
  filter_upwards [hst.2, hbb'] with v hInd hBC
  obtain ⟨hs, ht, _, hp⟩ := hInd
  obtain ⟨hb, hb', _, he⟩ := hBC
  refine ⟨hs, hb, ht, hb', ?_⟩
  exact (pairEulerPolynomial_of_inducedEulerPolynomial
    (s.eigenvalues v hs) (fun w : FinitePlacesAbove E v => t.eigenvalues w.1 (ht w))
    (b.eigenvalues v hb) (fun w => w.1.asIdeal.inertiaDeg (𝓞 F)) hp).trans (by
      simp only [he])

end Langlands.Automorphic.Unramified
