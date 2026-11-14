import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Automorphic.AssociatedGammaCompletedEquation
import Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement
import Langlands.Global.Factors.RelativeWeilAssemblyExceptional
import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.Global.AdelesSecondCountable
import Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion
import Langlands.Representation.RankinSelberg.LanglandsLFactor

/-!
# The completed cuspidal pair equation in the comparison-engine format

The archimedean pair L-factors are nonzero on a right half-plane, the finite pair
L-factors `1 / P_v(q_v^(-s))` with `P_v(0) = 1` are nonzero meromorphic and nonzero on a
right half-plane, and the finite epsilon monomials are nonzero meromorphic. With
`AssociatedGammaCompletedEquation`, a completed equation for a finite pair factor choice
gives the engine inputs at `univ.disjSum B` for every finite `B ⊇ S`, with the archimedean
factors lumped at one infinite place.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology Polynomial
open scoped BigOperators

namespace Langlands.Global.FunctionalEquationComparison

namespace CompletedEquationAdapter

open RelativeWeilEngine LocalFactor LocalFactor.Archimedean

/-! ### Archimedean factors -/

/-- A shifted Gamma block has no pole on a right half-plane. -/
theorem gammaBlock_denominator_ne_zero (b : GammaBlock) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → b.factor.denominator s ≠ 0 := by
  cases b with
  | real a =>
    refine ⟨-a.re, fun s hs h => ?_⟩
    obtain ⟨n, hn⟩ := (GammaBlock.real_isPole a s).mp h
    have hre := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero] at hre
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  | complex a =>
    refine ⟨-a.re, fun s hs h => ?_⟩
    obtain ⟨n, hn⟩ := (GammaBlock.complex_isPole a s).mp h
    have hre := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith

/-- A finite product of reciprocal-entire functions, each without poles on a right
half-plane, has no poles on a right half-plane. -/
theorem product_denominator_ne_zero : ∀ (Fs : List ReciprocalEntire),
    (∀ F ∈ Fs, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → F.denominator s ≠ 0) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (ReciprocalEntire.product Fs).denominator s ≠ 0
  | [], _ => ⟨0, fun s _ => by
      simp [ReciprocalEntire.product, ReciprocalEntire.one]⟩
  | F :: Fs, h => by
    obtain ⟨σ₁, h₁⟩ := h F List.mem_cons_self
    obtain ⟨σ₂, h₂⟩ := product_denominator_ne_zero Fs fun G hG => h G (List.mem_cons_of_mem _ hG)
    refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
    rw [ReciprocalEntire.product, ReciprocalEntire.denominator_mul]
    exact mul_ne_zero (h₁ s (lt_of_le_of_lt (le_max_left _ _) hs))
      (h₂ s (lt_of_le_of_lt (le_max_right _ _) hs))

/-- A finite Gamma product has no poles on a right half-plane. -/
theorem gammaProduct_denominator_ne_zero (blocks : List GammaBlock) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (gammaProduct blocks).denominator s ≠ 0 :=
  product_denominator_ne_zero _ fun F hF => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hF
    exact gammaBlock_denominator_ne_zero b

/-- The real pair L-factor has no poles on a right half-plane. -/
theorem realPairLFactor_denominator_ne_zero (xs ys : List RealBlock) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (realPairLFactor xs ys).denominator s ≠ 0 := by
  rw [realPairLFactor, realLFactor_eq_gammaProduct]
  exact gammaProduct_denominator_ne_zero _

/-- The complex pair L-factor has no poles on a right half-plane. -/
theorem complexPairLFactor_denominator_ne_zero (xs ys : List ComplexCharacterData) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (complexPairLFactor xs ys).denominator s ≠ 0 := by
  rw [complexPairLFactor, complexLFactor_eq_gammaProduct]
  exact gammaProduct_denominator_ne_zero _

/-- A finite product of reciprocals of denominators, each without zeros on a right
half-plane, is nonzero on a right half-plane. -/
theorem prod_inv_denominator_ne_zero {ι : Type*} [Fintype ι] (F : ι → ReciprocalEntire)
    (h : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (F i).denominator s ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∏ i, ((F i).denominator s)⁻¹ ≠ 0 := by
  choose σ hσ using h
  refine ⟨∑ i, |σ i|, fun s hs => Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero
    (hσ i s (lt_of_le_of_lt ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun i => |σ i|) (fun j _ => abs_nonneg _) hi)) hs))⟩

/-- A finite product of reciprocals of denominators has nonzero germ everywhere. -/
theorem nonzeroMeromorphic_prod_inv_denominator {ι : Type*} [Fintype ι]
    (F : ι → ReciprocalEntire) :
    NonzeroMeromorphic (fun s => ∏ i, ((F i).denominator s)⁻¹) :=
  NonzeroMeromorphic.finsetProd Finset.univ fun i _ =>
    NonzeroMeromorphic.inv (nonzeroMeromorphic_denominator (F i))

/-- An entire function without zeros has nonzero germ everywhere. -/
theorem nonzeroMeromorphic_of_differentiable_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ s, f s ≠ 0) : NonzeroMeromorphic f :=
  nonzeroMeromorphic_of_ne_zero_halfPlane (fun z => (hf.analyticAt z).meromorphicAt) 0
    fun s _ => h s

/-- The product of the reciprocal denominators of two finite families of reciprocal-entire
functions without poles on right half-planes is nonzero meromorphic and nonzero on a right
half-plane. This is the shape of the archimedean L-factors of the cuspidal equation. -/
theorem archimedeanL_spec {I J : Type*} [Fintype I] [Fintype J]
    (FR : I → ReciprocalEntire) (FC : J → ReciprocalEntire)
    (hR : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (FR i).denominator s ≠ 0)
    (hC : ∀ j, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (FC j).denominator s ≠ 0) :
    NonzeroMeromorphic (fun s => (∏ i, ((FR i).denominator s)⁻¹) *
        ∏ j, ((FC j).denominator s)⁻¹) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        (∏ i, ((FR i).denominator s)⁻¹) * ∏ j, ((FC j).denominator s)⁻¹ ≠ 0 := by
  obtain ⟨σ₁, h₁⟩ := prod_inv_denominator_ne_zero FR hR
  obtain ⟨σ₂, h₂⟩ := prod_inv_denominator_ne_zero FC hC
  exact ⟨NonzeroMeromorphic.mul (nonzeroMeromorphic_prod_inv_denominator FR)
      (nonzeroMeromorphic_prod_inv_denominator FC),
    max σ₁ σ₂, fun s hs => mul_ne_zero (h₁ s (lt_of_le_of_lt (le_max_left _ _) hs))
      (h₂ s (lt_of_le_of_lt (le_max_right _ _) hs))⟩

/-- The product of two finite families of unit-valued entire functions is nonzero
meromorphic. This is the shape of the archimedean epsilon factor of the cuspidal
equation. -/
theorem nonzeroMeromorphic_prod_units {I J : Type*} [Fintype I] [Fintype J]
    (eR : I → ℂ → ℂˣ) (eC : J → ℂ → ℂˣ)
    (hR : ∀ i, Differentiable ℂ (fun s => (eR i s : ℂ)))
    (hC : ∀ j, Differentiable ℂ (fun s => (eC j s : ℂ))) :
    NonzeroMeromorphic (fun s => (∏ i, (eR i s : ℂ)) * ∏ j, (eC j s : ℂ)) :=
  NonzeroMeromorphic.mul (NonzeroMeromorphic.finsetProd Finset.univ fun i _ =>
      nonzeroMeromorphic_of_differentiable_ne_zero (hR i) fun s => (eR i s).ne_zero)
    (NonzeroMeromorphic.finsetProd Finset.univ fun j _ =>
      nonzeroMeromorphic_of_differentiable_ne_zero (hC j) fun s => (eC j s).ne_zero)

/-- The archimedean pair L-factor of the cuspidal equation, for parameters at the real and
complex places, is nonzero meromorphic and nonzero on a right half-plane. -/
theorem cuspidalInfiniteL_spec {I J : Type*} [Fintype I] [Fintype J]
    (dR dR' : I → List RealBlock) (dC dC' : J → List ComplexCharacterData) :
    NonzeroMeromorphic (fun s => (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
          ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹ ≠ 0 :=
  archimedeanL_spec _ _ (fun v => realPairLFactor_denominator_ne_zero (dR v) (dR' v))
    fun v => complexPairLFactor_denominator_ne_zero (dC v) (dC' v)

/-- The archimedean pair epsilon factor of the cuspidal equation is nonzero
meromorphic. -/
theorem nonzeroMeromorphic_cuspidalInfiniteEpsilon {I J : Type*} [Fintype I] [Fintype J]
    (dR dR' : I → List RealBlock) (dC dC' : J → List ComplexCharacterData)
    (aR : I → ℝˣ) (aC : J → ℂˣ) :
    NonzeroMeromorphic (fun s =>
      (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
        ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
          (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)) :=
  nonzeroMeromorphic_prod_units _ _
    (fun _ => differentiable_realEpsilon _ _ _ _)
    fun _ => differentiable_complexEpsilon _ _ _ _

/-! ### Finite factors -/

/-- A polynomial with constant coefficient `1`, evaluated at `q^(-s)` with `q > 1`, is
nonzero on a right half-plane. -/
theorem eval_spectralPoint_ne_zero {q : ℕ} (hq : 1 < q) {P : ℂ[X]} (hP : P.coeff 0 = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P.eval (RankinSelberg.spectralPoint q s) ≠ 0 := by
  have h0 : P.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hP]
    exact one_ne_zero
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((P.continuous.continuousAt (x := 0)).eventually_ne h0)
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  refine ⟨-Real.logb q δ, fun s hs => hball ?_⟩
  rw [dist_zero_right, RankinSelberg.HighlyRamified.norm_spectralPoint hq0]
  calc (q : ℝ) ^ (-s.re) < (q : ℝ) ^ (Real.logb q δ) :=
        Real.rpow_lt_rpow_of_exponent_lt hqR (by linarith)
    _ = δ := Real.rpow_logb (by positivity) hqR.ne' hδ

/-- `s ↦ 1 / P(q^(-s))` is meromorphic for `q > 0`. -/
theorem meromorphic_inv_eval_spectralPoint {q : ℕ} (hq : 0 < q) (P : ℂ[X]) :
    Meromorphic (fun s => (P.eval (RankinSelberg.spectralPoint q s))⁻¹) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd : Differentiable ℂ (fun s => P.eval (RankinSelberg.spectralPoint q s)) :=
    P.differentiable.comp (differentiable_id.neg.const_cpow (Or.inl hq0))
  exact fun z => (hd.analyticAt z).meromorphicAt.inv

/-- `s ↦ 1 / P(q^(-s))` with `P(0) = 1`, `q > 1` is nonzero meromorphic and nonzero on a
right half-plane. -/
theorem inv_eval_spectralPoint_spec {q : ℕ} (hq : 1 < q) {P : ℂ[X]} (hP : P.coeff 0 = 1) :
    NonzeroMeromorphic (fun s => (P.eval (RankinSelberg.spectralPoint q s))⁻¹) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (P.eval (RankinSelberg.spectralPoint q s))⁻¹ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := eval_spectralPoint_ne_zero hq hP
  have hne : ∀ s : ℂ, σ < s.re → (P.eval (RankinSelberg.spectralPoint q s))⁻¹ ≠ 0 :=
    fun s hs => inv_ne_zero (hσ s hs)
  exact ⟨nonzeroMeromorphic_of_ne_zero_halfPlane
    (meromorphic_inv_eval_spectralPoint (lt_trans Nat.zero_lt_one hq) P) σ hne, σ, hne⟩

end CompletedEquationAdapter

end Langlands.Global.FunctionalEquationComparison

namespace Langlands.Global.CuspidalPairFunctionalEquation

namespace FinitePairFactorChoice

open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open Langlands.Global.FunctionalEquationComparison.CompletedEquationAdapter
open Langlands.Global.CompletionPadic
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

universe u uQ

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T Td : Automorphic.CuspidalOperatorRealization F r}
  {T' Td' : Automorphic.CuspidalOperatorRealization F t}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
  {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
  {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
  {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
  (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')

/-- The finite pair L-factor is nonzero meromorphic and nonzero on a right half-plane. -/
theorem finiteL_spec (v : FinitePlace F) :
    NonzeroMeromorphic (c.finiteL v) ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → c.finiteL v s ≠ 0 :=
  have hP : (c.lPolynomial v).coeff 0 = 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, hL⟩ := c.lPolynomial_spec v
    exact hL.coeff_zero
  inv_eval_spectralPoint_spec (one_lt_residueCardinality v) hP

/-- The finite dual pair L-factor is nonzero meromorphic and nonzero on a right
half-plane. -/
theorem finiteDualL_spec (v : FinitePlace F) :
    NonzeroMeromorphic (c.finiteDualL v) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → c.finiteDualL v s ≠ 0 :=
  have hP : (c.dualLPolynomial v).coeff 0 = 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, hL⟩ := c.dualLPolynomial_spec v
    exact hL.coeff_zero
  inv_eval_spectralPoint_spec (one_lt_residueCardinality v) hP

/-- The finite epsilon monomial is nonzero meromorphic. -/
theorem nonzeroMeromorphic_finiteEpsilon (v : FinitePlace F) :
    NonzeroMeromorphic (c.finiteEpsilon v) :=
  nonzeroMeromorphic_epsilonMonomial (residueCardinality v)
    (lt_trans Nat.zero_lt_one (one_lt_residueCardinality v)) (c.epsilon v).1 (c.epsilon v).2

/-- Outside a set where the choice is unramified, the finite epsilon factor is `1`. -/
theorem finiteEpsilon_eq_one {S : Finset (FinitePlace F)} (hS : c.IsUnramifiedOutside S)
    {v : FinitePlace F} (hv : v ∉ S) (s : ℂ) : c.finiteEpsilon v s = 1 := by
  simp [finiteEpsilon, (hS v hv).2.2]

/-- The completed equation of a finite pair factor choice, unramified outside `S`, with
archimedean products `Linf`, `Ldinf`, `εinf` that are nonzero meromorphic and with `Linf`,
`Ldinf` nonzero on a right half-plane, gives the comparison-engine inputs at
`univ.disjSum B` for every finite `B ⊇ S`, with the archimedean factors lumped at `w₀`. -/
theorem exists_engineInputs [DecidableEq (InfinitePlace F)]
    [DecidableEq (InfinitePlace F ⊕ FinitePlace F)] (S B : Finset (FinitePlace F))
    (hSB : S ⊆ B) (hS : c.IsUnramifiedOutside S) (Linf Ldinf εinf : ℂ → ℂ)
    (hLinf : NonzeroMeromorphic Linf) (hLdinf : NonzeroMeromorphic Ldinf)
    (hεinf : NonzeroMeromorphic εinf)
    (hLne : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Linf s ≠ 0 ∧ Ldinf s ≠ 0)
    (hC : c.CompletedEquationHolds S Linf Ldinf εinf) (w₀ : InfinitePlace F) :
    ∃ (σ' : ℝ) (Lp Lpd : ℂ → ℂ),
      Admissible (FiniteEulerData.mk (Sum.elim (lumpedArch w₀ Linf Ldinf εinf)
          fun v => ⟨c.finiteL v, c.finiteDualL v, c.finiteEpsilon v⟩) Lp Lpd)
        ((Finset.univ : Finset (InfinitePlace F)).disjSum B) ∧
      HasEulerProductsOutside (FiniteEulerData.mk (Sum.elim (lumpedArch w₀ Linf Ldinf εinf)
          fun v => ⟨c.finiteL v, c.finiteDualL v, c.finiteEpsilon v⟩) Lp Lpd)
        ((Finset.univ : Finset (InfinitePlace F)).disjSum B) σ' ∧
      FunctionalEquation (FiniteEulerData.mk (Sum.elim (lumpedArch w₀ Linf Ldinf εinf)
          fun v => ⟨c.finiteL v, c.finiteDualL v, c.finiteEpsilon v⟩) Lp Lpd)
        ((Finset.univ : Finset (InfinitePlace F)).disjSum B) := by
  have := Langlands.Global.finitePlace_countable F
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hprod, hfe⟩ := hC
  obtain ⟨σL, hσL⟩ := hLne
  obtain ⟨σ', h1, h2, h3⟩ := functionalEquation_of_completedEquation
    (lumpedArch w₀ Linf Ldinf εinf) c.finiteL c.finiteDualL c.finiteEpsilon Linf Ldinf εinf
    (lumpedArch_nonzeroMeromorphic w₀ hLinf hLdinf hεinf)
    (lumpedArch_prod_lFactor w₀ Linf Ldinf εinf)
    (lumpedArch_prod_dualLFactor w₀ Linf Ldinf εinf)
    (lumpedArch_prod_epsilonFactor w₀ Linf Ldinf εinf) σL hσL
    (fun v => ⟨(c.finiteL_spec v).1, (c.finiteDualL_spec v).1,
      c.nonzeroMeromorphic_finiteEpsilon v⟩)
    (fun v => by
      obtain ⟨σ₁, h₁⟩ := (c.finiteL_spec v).2
      obtain ⟨σ₂, h₂⟩ := (c.finiteDualL_spec v).2
      exact ⟨max σ₁ σ₂, fun s hs => ⟨h₁ s (lt_of_le_of_lt (le_max_left _ _) hs),
        h₂ s (lt_of_le_of_lt (le_max_right _ _) hs)⟩⟩)
    S B hSB (fun v _ hvS s => c.finiteEpsilon_eq_one hS hvS s) σ Λ Λd hΛ hΛd hprod hfe
  exact ⟨σ', _, _, h1, h2, h3⟩

/-- `exists_engineInputs` for the archimedean factors of the published cuspidal
equation `CuspidalPairGlobalFunctionalEquationStatement`: the archimedean hypotheses hold
for every choice of parameters and additive components. -/
theorem exists_engineInputs_cuspidal [DecidableEq (InfinitePlace F)]
    [DecidableEq (InfinitePlace F ⊕ FinitePlace F)] {I J : Type*} [Fintype I] [Fintype J]
    (S B : Finset (FinitePlace F)) (hSB : S ⊆ B) (hS : c.IsUnramifiedOutside S)
    (aR : I → ℝˣ) (aC : J → ℂˣ) (dR dR' dRd dRd' : I → List RealBlock)
    (dC dC' dCd dCd' : J → List ComplexCharacterData)
    (hC : c.CompletedEquationHolds S
      (fun s => (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹)
      (fun s => (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹)
      (fun s => (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
        ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
          (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)))
    (w₀ : InfinitePlace F) :
    ∃ (σ' : ℝ) (Lp Lpd : ℂ → ℂ),
      let arch := lumpedArch w₀
        (fun s => (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
          ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹)
        (fun s => (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
          ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹)
        (fun s => (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
          ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
            (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ))
      let D := FiniteEulerData.mk (Sum.elim arch
        fun v => ⟨c.finiteL v, c.finiteDualL v, c.finiteEpsilon v⟩) Lp Lpd
      Admissible D ((Finset.univ : Finset (InfinitePlace F)).disjSum B) ∧
        HasEulerProductsOutside D ((Finset.univ : Finset (InfinitePlace F)).disjSum B) σ' ∧
        FunctionalEquation D ((Finset.univ : Finset (InfinitePlace F)).disjSum B) := by
  obtain ⟨hL, σ₁, h₁⟩ := cuspidalInfiniteL_spec dR dR' dC dC'
  obtain ⟨hLd, σ₂, h₂⟩ := cuspidalInfiniteL_spec dRd dRd' dCd dCd'
  exact c.exists_engineInputs S B hSB hS _ _ _ hL hLd
    (nonzeroMeromorphic_cuspidalInfiniteEpsilon dR dR' dC dC' aR aC)
    ⟨max σ₁ σ₂, fun s hs => ⟨h₁ s (lt_of_le_of_lt (le_max_left _ _) hs),
      h₂ s (lt_of_le_of_lt (le_max_right _ _) hs)⟩⟩ hC w₀

end FinitePairFactorChoice

end Langlands.Global.CuspidalPairFunctionalEquation
