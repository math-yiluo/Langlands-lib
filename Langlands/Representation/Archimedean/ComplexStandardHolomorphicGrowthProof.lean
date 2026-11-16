import Langlands.Representation.Archimedean.ComplexHolomorphicTestFunctions
import Langlands.Representation.Archimedean.ComplexLinkedSmallGrowthProof

/-!
# Proof of `ComplexStandardHolomorphicGrowthStatement`

The products `u_α = ∏_i ι(hol Y_i)^{α_i}` of the `2N = n(n-1)` elements `Y_i = symbMat i`
act on the `U(n)`-finite principal series through linearly independent operators
(`coeff_eq_zero_wordOp`): a vanishing combination `Σ c_α u_α` vanishes on the test functions,
so by the jets (`hasJet_holWord`, `hasJet_testFun`) the corresponding combination of differential
operators vanishes on all polynomials in `v`, hence on all of `Pol n`
(`eq_zero_of_kills_rename`); its longest words then give a vanishing combination of the symbol
products `prodSymb α` (`sum_prod_sym_eq_zero`), which are linearly independent
(`linearIndependent_prodSymb`). Counting the `α` with entries `≤ d / (M + 1)` gives
`finrank ≥ (d + 1)^{n(n-1)} / (M + 1)^{M}`.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace HolomorphicGrowth

open MvPolynomial Langlands.GeneralLinear Langlands.Archimedean.NoncompactPicture
open Langlands.Archimedean.MomentSymbols Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.AdjacentGrowth Langlands.Archimedean.LevelFunctions
open Langlands.Archimedean.HolomorphicJets Langlands.Algebra.UniversalEnveloping
open Langlands.Archimedean.ComplexLinkedLanglandsQuotientGrowth

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {χ : ℕ → ℂˣ → ℂ}

/-- The `U(n)`-finite principal series. -/
abbrev KF (n : ℕ) (χ : ℕ → ℂˣ → ℂ) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)

theorem coe_principalSeriesLie_hol (X : Matrix (Fin n) (Fin n) ℂ) (f : KF n χ) :
    ((principalSeriesLie ℂ n χ (hol X) f : KF n χ) : Langlands.GeneralLinear n ℂ → ℂ) =
      holDeriv X f := by
  rw [hol, map_smul, map_sub, tmul_eq_smul Complex.I (Complex.I • X), map_smul]
  funext g
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
    Pi.smul_apply, Pi.sub_apply, principalSeriesLie_one_tmul_apply_coe, holDeriv, smul_eq_mul]

/-- The composition of holomorphic right derivatives along a list. -/
def holWord : List (Matrix (Fin n) (Fin n) ℂ) → (Langlands.GeneralLinear n ℂ → ℂ) →
    (Langlands.GeneralLinear n ℂ → ℂ)
  | [], F => F
  | X :: L, F => holDeriv X (holWord L F)

/-- The product `∏ ι(hol X)` along a list. -/
def uWord (L : List (Matrix (Fin n) (Fin n) ℂ)) :
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  (L.map fun X => UniversalEnvelopingAlgebra.ι ℂ (hol X)).prod

theorem coe_envelopingAction_uWord (L : List (Matrix (Fin n) (Fin n) ℂ)) (f : KF n χ) :
    ((envelopingAction (principalSeriesLie ℂ n χ) (uWord L) f : KF n χ) :
      Langlands.GeneralLinear n ℂ → ℂ) = holWord L f := by
  induction L with
  | nil => simp [uWord, holWord]
  | cons X L ih =>
    rw [uWord, List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply,
      UniversalEnvelopingAlgebra.lift_ι_apply, coe_principalSeriesLie_hol, ← uWord, ih]
    rfl

theorem holDeriv_mem {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ principalSeries ℂ n χ)
    (X : Matrix (Fin n) (Fin n) ℂ) : holDeriv X F ∈ principalSeries ℂ n χ :=
  Submodule.smul_mem _ _ (Submodule.sub_mem _ (rightDerivative_mem_principalSeries χ hF X)
    (Submodule.smul_mem _ _ (rightDerivative_mem_principalSeries χ hF _)))

theorem holWord_mem {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ principalSeries ℂ n χ) :
    ∀ L : List (Matrix (Fin n) (Fin n) ℂ), holWord L F ∈ principalSeries ℂ n χ
  | [] => hF
  | X :: L => holDeriv_mem (holWord_mem hF L) X

theorem hasJet_holWord (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k)) {σ : Fin n → ℂ}
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ principalSeries ℂ n χ) {Q : Pol n}
    (hJ : HasJet σ F Q) :
    ∀ L : List (Matrix (Fin n) (Fin n) ℂ),
      HasJet σ (holWord L F) (evalWord (L.map (opDataH (alphaOf l t))) Q)
  | [] => hJ
  | X :: L => hasJet_holDeriv l t hχ (holWord_mem hF L) (hasJet_holWord l t hχ hF hJ L) X

/-! ## Membership in the holomorphic filtration -/

theorem uWord_mem_pow (L : List (Matrix (Fin n) (Fin n) ℂ)) :
    uWord L ∈ (Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
      UniversalEnvelopingAlgebra.ι ℂ (hol X)) ⊔ 1) ^ L.length := by
  induction L with
  | nil => simpa [uWord] using Submodule.mem_one.2 ⟨1, map_one _⟩
  | cons X L ih =>
    rw [uWord, List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact Submodule.mul_mem_mul (Submodule.mem_sup_left (Submodule.subset_span ⟨X, rfl⟩)) ih

theorem uWord_mem_holFiltration (L : List (Matrix (Fin n) (Fin n) ℂ)) {d : ℕ}
    (hL : L.length ≤ d) : uWord L ∈ holFiltration n d := by
  have h1 : (1 : Submodule ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ))) ≤
      Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
        UniversalEnvelopingAlgebra.ι ℂ (hol X)) ⊔ 1 := le_sup_right
  rw [holFiltration, ← Nat.add_sub_cancel' hL, pow_add]
  have h2 : (1 : Submodule ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ))) ≤
      (Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
        UniversalEnvelopingAlgebra.ι ℂ (hol X)) ⊔ 1) ^ (d - L.length) := by
    induction (d - L.length) with
    | zero => rw [pow_zero]
    | succ k ihk =>
      rw [pow_succ]
      calc (1 : Submodule ℂ _) = 1 * 1 := (one_mul _).symm
        _ ≤ _ := mul_le_mul' ihk h1
  have := Submodule.mul_mem_mul (uWord_mem_pow L) (h2 (Submodule.mem_one.2 ⟨1, map_one _⟩))
  rwa [mul_one] at this

/-! ## The words of the symbols -/

/-- The list with `α_i` copies of `symbMat i`. -/
def wordOf (α : Lw n ⊕ Lw n → ℕ) : List (Matrix (Fin n) (Fin n) ℂ) :=
  (Finset.univ : Finset (Lw n ⊕ Lw n)).toList.foldr
    (fun i acc => List.replicate (α i) (symbMat i) ++ acc) []

theorem foldr_prod {M : Type*} [CommMonoid M] (α : Lw n ⊕ Lw n → ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ → M) (L : List (Lw n ⊕ Lw n)) :
    ((L.foldr (fun i acc => List.replicate (α i) (symbMat i) ++ acc) []).map f).prod =
      (L.map fun i => f (symbMat i) ^ α i).prod := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldr_cons, List.map_append, List.prod_append, ih, List.map_replicate,
      List.prod_replicate, List.map_cons, List.prod_cons]

theorem foldr_length (α : Lw n ⊕ Lw n → ℕ) (L : List (Lw n ⊕ Lw n)) :
    (L.foldr (fun i acc => List.replicate (α i) (symbMat i) ++ acc) []).length =
      (L.map α).sum := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [List.foldr_cons, List.length_append, ih, List.length_replicate,
      List.map_cons, List.sum_cons]

theorem length_wordOf (α : Lw n ⊕ Lw n → ℕ) : (wordOf α).length = ∑ i, α i := by
  rw [wordOf, foldr_length, Finset.sum_map_toList]

theorem prod_sym_wordOf (a : Fin n → ℂ) (α : Lw n ⊕ Lw n → ℕ) :
    (((wordOf α).map (opDataH a)).map sym).prod = prodSymb α := by
  rw [List.map_map, wordOf, foldr_prod, Finset.prod_map_toList, prodSymb]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Function.comp_apply, sym_opDataH_symbMat]

/-! ## The level data of a character -/

section Data

variable (n : ℕ) (l : ℕ → ℤ) (t : ℕ → ℂ)

/-- The level increments of the weights. -/
def eL (m : ℕ) : ℤ := l m - shift l m

/-- Holomorphic determinant factors at each level. -/
def hL (m : ℕ) : ℕ := (eL l m).toNat

/-- Antiholomorphic determinant factors at each level. -/
def bL (m : ℕ) : ℕ := (-eL l m).toNat

/-- The shifted exponents. -/
def tauL (k : ℕ) : ℂ := t k + ((n : ℂ) - 1) / 2 - (k : ℂ)

/-- The level increments of the shifted exponents. -/
def dtL (m : ℕ) : ℂ := tauL n t m - shift (tauL n t) m

theorem hl_L : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
    ((hL l m : ℤ) - bL l m) = l k := by
  intro k
  rw [sum_filter_le_eq (fun m => (hL l m : ℤ) - bL l m) k]
  simp only [hL, bL, Int.toNat_sub_toNat_neg, eL]
  exact sum_range_sub_shift l k

theorem hτ_L : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
    dtL n t m = t k + ((n : ℂ) - 1) / 2 - (k : ℕ) := by
  intro k
  rw [sum_filter_le_eq (dtL n t) k]
  exact sum_range_sub_shift (tauL n t) k

end Data

/-! ## Independence -/

/-- **The operators of the words of the symbols are linearly independent**: a combination
vanishing on all `U(n)`-finite functions has zero coefficients. -/
theorem coeff_eq_zero_wordOp (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k)) {ι : Type*}
    (A : ι → (Lw n ⊕ Lw n → ℕ)) (hA : Function.Injective A) (s : Finset ι) (c : ι → ℂ)
    (hc : ∀ f : KF n χ, ∑ i ∈ s, c i • holWord (wordOf (A i)) f = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  set σ : Fin n → ℂ := gramExp (hL l) (bL l) (dtL n t)
  set w : ι → List (OpData n) := fun i => (wordOf (A i)).map (opDataH (alphaOf l t))
  -- the combination vanishes on the jets of the test functions
  have h1 : ∀ γ : Lw n → ℕ, ∑ i ∈ s, c i • evalWord (w i) (ιP (testPoly γ)) = 0 := by
    intro γ
    have hmem := testFun_mem_kFiniteFunctions γ (hL l) (bL l) (dtL n t) l t hχ (hl_L n l)
      (hτ_L n t)
    have hPS : testFun γ (hL l) (bL l) (dtL n t) ∈ principalSeries ℂ n χ :=
      (Submodule.mem_inf.1 hmem).1
    have h0 := hc ⟨_, hmem⟩
    have hJ : HasJet σ (∑ i ∈ s, c i • holWord (wordOf (A i)) (testFun γ (hL l) (bL l) (dtL n t)))
        (∑ i ∈ s, c i • evalWord (w i) (ιP (testPoly γ))) :=
      HasJet.sum s _ _ fun i _ =>
        (hasJet_holWord l t hχ hPS (hasJet_testFun γ (hL l) (bL l) (dtL n t)) _).smul (c i)
    rw [h0] at hJ
    exact (hJ.unique hasJet_zero)
  -- hence on all polynomials in `v`
  have h2 : ∀ Q : Hol n, ∑ i ∈ s, c i • evalWord (w i) (rename vV Q) = 0 := by
    intro Q
    induction Q using MvPolynomial.induction_on' with
    | monomial u a' =>
      have hm : (monomial u a' : Hol n) = a' • testPoly (fun p => u p) := by
        rw [testPoly_eq, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), smul_eq_C_mul]
      rw [hm, map_smul]
      simp only [map_smul, smul_comm (c _) a']
      rw [← Finset.smul_sum, h1, smul_zero]
    | add p q hp hq =>
      simp only [map_add, smul_add, Finset.sum_add_distrib, hp, hq, add_zero]
  have h3 := eq_zero_of_kills_rename s c w h2
  -- the longest words
  intro i hi
  by_contra hci
  set s' := s.filter (fun j => c j ≠ 0)
  have his' : i ∈ s' := Finset.mem_filter.2 ⟨hi, hci⟩
  obtain ⟨j, hj, hmax⟩ := s'.exists_max_image (fun j => (w j).length) ⟨i, his'⟩
  have h4 : ∀ P, ∑ k ∈ s', c k • evalWord (w k) P = 0 := fun P => by
    refine (Finset.sum_filter _ _).trans ((Finset.sum_congr rfl fun k _ => ?_).trans (h3 P))
    split_ifs with h
    · rfl
    · rw [not_not.1 h, zero_smul]
  have h5 := sum_prod_sym_eq_zero s' c w h4 (w j).length fun k hk => hmax k hk
  simp only [w, prod_sym_wordOf] at h5
  have hli := linearIndependent_prodSymb.comp A hA
  have := linearIndependent_iff'.1 hli _ c h5 j (Finset.mem_filter.2 ⟨hj, rfl⟩)
  exact (Finset.mem_filter.1 hj).2 this

/-! ## The count -/

/-- **Proof of `ComplexStandardHolomorphicGrowthStatement`.** -/
theorem complexStandardHolomorphicGrowth : ComplexStandardHolomorphicGrowthStatement := by
  intro n ds
  have hχ := LinkedSmallGrowth.complexPositionCharacter_eq_phase ds
  have hM : n * (n - 1) = Fintype.card (Lw n ⊕ Lw n) := by
    rw [Fintype.card_sum, ← card_Lw_mul_two]; ring
  set M := Fintype.card (Lw n ⊕ Lw n)
  refine ⟨1 / ((M : ℝ) + 1) ^ M, by positivity, fun d => ?_⟩
  set q := d / (M + 1)
  let A : (Lw n ⊕ Lw n → Fin (q + 1)) → (Lw n ⊕ Lw n → ℕ) := fun α i => α i
  have hA : Function.Injective A := fun α β h => funext fun i => Fin.ext (congrFun h i)
  set W := (holFiltration n d).map (envelopingAction (complexStandardLie n ds)).toLinearMap
  have hlen : ∀ α, (wordOf (A α)).length ≤ d := by
    intro α
    rw [length_wordOf]
    calc ∑ i, A α i ≤ ∑ _i : Lw n ⊕ Lw n, q :=
          Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.1 (α i).2
      _ = M * q := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ (M + 1) * q := Nat.mul_le_mul_right _ (Nat.le_succ M)
      _ ≤ d := Nat.mul_div_le d (M + 1)
  have hmemW : ∀ α, envelopingAction (complexStandardLie n ds) (uWord (wordOf (A α))) ∈ W :=
    fun α => Submodule.mem_map_of_mem (uWord_mem_holFiltration _ (hlen α))
  let Φ : ((Lw n ⊕ Lw n → Fin (q + 1)) → ℂ) →ₗ[ℂ] W :=
    Fintype.linearCombination ℂ (fun α => (⟨_, hmemW α⟩ : W))
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun c hc => ?_
    rw [Fintype.linearCombination_apply] at hc
    have hc' : ∀ f : KF n (complexPositionCharacter ds),
        ∑ α, c α • holWord (wordOf (A α)) f = 0 := by
      intro f
      have := congrArg (fun T : W => (((T : Module.End ℂ _) f : KF n _) :
        Langlands.GeneralLinear n ℂ → ℂ)) hc
      simpa [Submodule.coe_sum, coe_envelopingAction_uWord] using this
    funext α
    exact coeff_eq_zero_wordOp (LinkedSmallGrowth.posWeight ds)
      (LinkedSmallGrowth.posExponent ds) hχ A hA Finset.univ c hc' α (Finset.mem_univ α)
  have hcard := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin] at hcard
  have hq : ((d : ℝ) + 1) / ((M : ℝ) + 1) ≤ (q : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity)]
    have := Nat.lt_mul_div_succ d (Nat.succ_pos M)
    have h' : (d : ℝ) + 1 ≤ ((M : ℝ) + 1) * ((q : ℝ) + 1) := by exact_mod_cast this
    linarith
  calc 1 / ((M : ℝ) + 1) ^ M * ((d : ℝ) + 1) ^ (n * (n - 1))
      = (((d : ℝ) + 1) / ((M : ℝ) + 1)) ^ M := by rw [hM, div_pow]; ring
    _ ≤ ((q : ℝ) + 1) ^ M := pow_le_pow_left₀ (by positivity) hq M
    _ ≤ _ := by exact_mod_cast hcard

end HolomorphicGrowth

end Langlands.Archimedean
