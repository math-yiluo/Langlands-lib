import Langlands.Global.Factors.RelativeWeilEngine
import Langlands.LocalFactor.Archimedean.GammaExponentComparison
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-! # The finite epsilon bases from two completed functional equations -/

noncomputable section

open Filter Topology
open scoped BigOperators Topology

namespace Langlands.Global.FunctionalEquationComparison

open RelativeWeilEngine LocalFactor.Archimedean

universe u v

/-- The positive real base of the product of finite epsilon monomials. -/
def finiteEpsilonBase {Q : Type*} (S : Finset Q) (q : Q → ℕ) (e : Q → ℂˣ × ℤ) : ℝ :=
  ∏ w ∈ S, (q w : ℝ) ^ (e w).2

theorem finiteEpsilonBase_pos {Q : Type*} (S : Finset Q) (q : Q → ℕ) (e : Q → ℂˣ × ℤ)
    (hq : ∀ w ∈ S, 0 < q w) : 0 < finiteEpsilonBase S q e := by
  exact Finset.prod_pos (fun w hw => zpow_pos (by exact_mod_cast hq w hw) _)

/-- The actual pair epsilon monomials combine into a complex unit times the
negative spectral power of the product of their residue-cardinality powers. -/
theorem prod_epsilonMonomial_eq {Q : Type*} (S : Finset Q) (q : Q → ℕ) (e : Q → ℂˣ × ℤ)
    (hq : ∀ w ∈ S, 0 < q w) (z : ℂ) :
    ∏ w ∈ S, RankinSelberg.epsilonMonomial (q w) (e w).1 (e w).2 z =
      ((∏ w ∈ S, (e w).1 : ℂˣ) : ℂ) * (finiteEpsilonBase S q e : ℂ) ^ (-z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finiteEpsilonBase]
  | @insert w S hw ih =>
    have hqw := hq w (Finset.mem_insert_self w S)
    have hqS : ∀ a ∈ S, 0 < q a := fun a ha => hq a (Finset.mem_insert_of_mem ha)
    have hpos : 0 < (q w : ℝ) ^ (e w).2 := zpow_pos (by exact_mod_cast hqw) _
    have hv : (RankinSelberg.spectralPoint (q w) z) ^ (e w).2 =
        (((q w : ℝ) ^ (e w).2 : ℝ) : ℂ) ^ (-z) := by
      rw [RankinSelberg.spectralPoint, Complex.ofReal_zpow, Complex.ofReal_natCast,
        ← Complex.cpow_int_mul]
      apply Complex.cpow_int_mul'
      · simp [Complex.natCast_arg, Real.pi_pos]
      · simp [Complex.natCast_arg, Real.pi_pos.le]
    have hbase : finiteEpsilonBase (insert w S) q e = (q w : ℝ) ^ (e w).2 *
        finiteEpsilonBase S q e := Finset.prod_insert hw
    rw [Finset.prod_insert hw, ih hqS, Finset.prod_insert hw, hbase, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hpos.le (finiteEpsilonBase_pos S q e hqS).le,
      Units.val_mul, RankinSelberg.epsilonMonomial, hv]
    ring

local notation "Γvalue(" blocks ")" => fun z : ℂ => (LocalFactor.ReciprocalEntire.denominator (gammaProduct blocks) z)⁻¹

/-- Two completed equations with common forward and dual Euler-product values
on a right half-plane have equal finite epsilon bases when the archimedean L
products have matching real-Gamma counts and the two archimedean epsilon
products differ by a constant unit. Both choices of finite place index are free. -/
def FiniteEpsilonBaseComparisonStatement : Prop :=
  ∀ (Q : Type u) (Q' : Type v)
    (S : Finset Q) (S' : Finset Q')
    (l ld e : Q → ℂ → ℂ) (l' ld' e' : Q' → ℂ → ℂ)
    (A B Ad Bd : List GammaBlock) (Ae Be : ℂ → ℂ),
    HasGlobalEquation l ld e Γvalue(A) Γvalue(Ad) Ae S →
    HasGlobalEquation l' ld' e' Γvalue(B) Γvalue(Bd) Be S' →
    (∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∃ p pd : ℂ,
      HasProd (fun w => l w z) p ∧ HasProd (fun w => l' w z) p ∧
      HasProd (fun w => ld w z) pd ∧ HasProd (fun w => ld' w z) pd) →
    (A.flatMap GammaBlock.realShifts).length = (B.flatMap GammaBlock.realShifts).length →
    (Ad.flatMap GammaBlock.realShifts).length = (Bd.flatMap GammaBlock.realShifts).length →
    (∃ c : ℂˣ, ∀ z, Ae z = (c : ℂ) * Be z ∧ Be z ≠ 0) →
    ∀ (MA MB : ℝ), 0 < MA → 0 < MB → ∀ (cA cB : ℂˣ),
      (∀ z, ∏ w ∈ S, e w z = (cA : ℂ) * (MA : ℂ) ^ (-z)) →
      (∀ z, ∏ w ∈ S', e' w z = (cB : ℂ) * (MB : ℂ) ^ (-z)) →
      MA = MB

theorem finiteEpsilonBaseComparison : FiniteEpsilonBaseComparisonStatement.{u, v} := by
  intro Q Q' S S' l ld e l' ld' e' A B Ad Bd Ae Be hA hB hprod hAB hAdBd hAe MA MB
    hMA hMB cA cB heA heB
  obtain ⟨σA, L, Ld, hL, hLd, hprodA, hFEA⟩ := hA
  obtain ⟨σB, L', Ld', hL', hLd', hprodB, hFEB⟩ := hB
  obtain ⟨σ, hprod⟩ := hprod
  obtain ⟨archConstant, hArch⟩ := hAe
  have hsame : ∀ z : ℂ, max (max σA σB) σ < z.re → L z = L' z ∧ Ld z = Ld' z := by
    intro z hz
    obtain ⟨p, pd, hp, hp', hpd, hpd'⟩ := hprod z (lt_of_le_of_lt (le_max_right _ _) hz)
    have hzA := lt_of_le_of_lt ((le_max_left σA σB).trans (le_max_left _ σ)) hz
    have hzB := lt_of_le_of_lt ((le_max_right σA σB).trans (le_max_left _ σ)) hz
    obtain ⟨⟨hPA, _⟩, hPdA, _⟩ := hprodA z hzA
    obtain ⟨⟨hPB, _⟩, hPdB, _⟩ := hprodB z hzB
    exact ⟨(hPA.unique hp).trans (hPB.unique hp').symm,
      (hPdA.unique hpd).trans (hPdB.unique hpd').symm⟩
  have hsameL : MeromorphicEq L L' := eq_on_halfplane_meromorphicEq hL hL' (fun z hz => (hsame z hz).1)
  have hsameD : MeromorphicEq Ld Ld' :=
    eq_on_halfplane_meromorphicEq hLd hLd' (fun z hz => (hsame z hz).2)
  have hLnz := nonzeroMeromorphic_of_ne_zero_halfPlane hL σA (fun z hz => (hprodA z hz).1.2)
  have hMB₀ : (MB : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMB.ne'
  let ratio : ℂˣ := archConstant * cA / cB
  have hcross : ∀ᶠ z in codiscrete ℂ,
      Γvalue(A) z * Γvalue(Bd) (1 - z) =
        (ratio : ℂ) * ((MA / MB : ℝ) : ℂ) ^ (-z) * (Γvalue(B) z * Γvalue(Ad) (1 - z)) := by
    apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
    intro w
    filter_upwards [hFEA w, hFEB w, hsameL w, hsameD.reflect w, hLnz.eventually_ne_zero w]
      with z hzA hzB hzL hzLd hz0
    obtain ⟨hzArch, hzBe⟩ := hArch z
    have hpow : (MB : ℂ) ^ (-z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hMB₀)
    have hratio : (cB : ℂ) * (MB : ℂ) ^ (-z) *
        ((ratio : ℂ) * ((MA / MB : ℝ) : ℂ) ^ (-z)) =
          (archConstant : ℂ) * ((cA : ℂ) * (MA : ℂ) ^ (-z)) := by
      dsimp only [ratio]
      rw [Units.val_div_eq_div_val, Units.val_mul, Complex.ofReal_div,
        Complex.div_cpow_ofReal_nonneg hMA.le hMB.le]
      field_simp [cB.ne_zero, hpow]
    have hcancel : L z * (Be z * ((cB : ℂ) * (MB : ℂ) ^ (-z))) ≠ 0 :=
      mul_ne_zero hz0 (mul_ne_zero hzBe (mul_ne_zero cB.ne_zero hpow))
    apply mul_left_cancel₀ hcancel
    simp only [heA, hzArch] at hzA
    rw [← hzL, ← hzLd, heB] at hzB
    rw [show L z * (Be z * ((cB : ℂ) * (MB : ℂ) ^ (-z))) *
        ((ratio : ℂ) * ((MA / MB : ℝ) : ℂ) ^ (-z) * (Γvalue(B) z * Γvalue(Ad) (1 - z))) =
        L z * Be z * ((cB : ℂ) * (MB : ℂ) ^ (-z) *
          ((ratio : ℂ) * ((MA / MB : ℝ) : ℂ) ^ (-z))) *
            (Γvalue(B) z * Γvalue(Ad) (1 - z)) by ring, hratio]
    linear_combination hzA * (Be z * ((cB : ℂ) * (MB : ℂ) ^ (-z)) * Γvalue(Bd) (1 - z)) -
      hzB * ((archConstant : ℂ) * Be z * ((cA : ℂ) * (MA : ℂ) ^ (-z)) * Γvalue(Ad) (1 - z))
  exact (div_eq_one_iff_eq hMB.ne').mp
    (archimedeanGammaExponentComparison A B Ad Bd hAB hAdBd _ (div_pos hMA hMB) ratio hcross)

end Langlands.Global.FunctionalEquationComparison
