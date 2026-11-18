import Langlands.Global.RankinSelberg.EqualEulerPointwise
import Langlands.Global.RankinSelberg.UnequalKernelLocalPoint
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationStatement
import Langlands.Global.RankinSelberg.UnequalUnfoldingStatement
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationStatement
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Representation.RankinSelberg.UnramifiedUnequalLocalSum
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput

/-! # Reduction of the unequal-rank partial Euler factorization

`UnequalEulerFactorizationStatement` (Cogdell 2004, §2.2 with Theorem 3.3) follows from three
premises: the factorization of global Whittaker functions at an unramified place
(`UnramifiedWhittakerFactorizationStatement`), the one-place Iwasawa cell decomposition of the
Whittaker quotient measure (`WhittakerCellDecompositionStatement`), and the unfolding statement
(`UnequalUnfoldingStatement`), which supplies the absolute convergence of the global Whittaker
integral. See the paired Markdown for the argument.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorization

open LocalPointFactorization
open CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.GeneralLinear.Iwasawa (torus torus_val IsUniformizingElement IsIntegrallyTrivial)
open Langlands.GeneralLinear.Spherical (sphericalWhittaker)
open Langlands.RankinSelberg.UnramifiedUnequalLocalSum (padZeroWeight localTerm)

local instance reductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance reductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### Weights -/

/-- `diag(ϖ^λ, 1_(r-t)) = ϖ^(λ, 0)`. -/
theorem padGL_torus {K : Type*} [Field K] {r t : ℕ} (hle : t + 1 ≤ r + 1) (ϖ : Kˣ)
    (lam : Fin (t + 1) → ℤ) :
    padGL hle (torus ϖ lam) = torus ϖ (padZeroWeight r lam) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Unfolding.padGL_apply, torus_val, torus_val]
  by_cases hi : (i : ℕ) < t + 1
  · rw [dite_eq_left hi]
    by_cases hj : (j : ℕ) < t + 1
    · rw [dite_eq_left hj]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
          RankinSelberg.UnramifiedUnequalLocalSum.padZeroWeight_of_lt _ _ hi]
      · have hne : (⟨i, hi⟩ : Fin (t + 1)) ≠ ⟨j, hj⟩ := fun e =>
          hij (Fin.ext (Fin.mk.inj e))
        rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hij]
    · rw [dite_eq_right hj, Matrix.diagonal_apply_ne]
      intro e
      exact hj (e ▸ hi)
  · rw [dite_eq_right hi]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, Matrix.diagonal_apply_eq,
        RankinSelberg.UnramifiedUnequalLocalSum.padZeroWeight_of_le _ _ (by omega), zpow_zero,
        Units.val_one]
    · rw [ite_eq_right hij, Matrix.diagonal_apply_ne _ hij]

/-! ### Integrality at an unramified place -/

variable {F : Type u} [Field F] [NumberField F]

/-- `GL(𝒪_v)` is the integral subgroup of the canonical valuation of `F_v`. -/
theorem mem_integralSubgroup_of_mem_localIntegral (v : FinitePlace F) {m : ℕ}
    {k : FiniteLocalGL F (m + 1) v} (hk : k ∈ FiniteAdelicGL.localIntegral F (m + 1) v) :
    k ∈ Langlands.Conductor.integralSubgroup
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel).integer m := by
  rw [FiniteAdelicGL.mem_localIntegral] at hk
  rw [Langlands.Conductor.mem_integralSubgroup,
    ← integer_eq_of_isEquiv (valued_isEquiv_canonical v)]
  exact ⟨fun i j => (Valuation.mem_integer_iff _ _).2 (hk.1 i j),
    fun i j => (Valuation.mem_integer_iff _ _).2 (hk.2 i j)⟩

/-- For a component `ψ_v` of conductor `𝒪_v`, the standard character of `ψ_v` and its inverse
are trivial on the integral unitriangular matrices. -/
theorem isIntegrallyTrivial_standardCharacters (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hcond : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (n : ℕ) :
    IsIntegrallyTrivial
        (@ValuativeRel.valuation _ _
          (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel)
        (@Whittaker.standardCharacter _ _
          (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n) ∧
      IsIntegrallyTrivial
        (@ValuativeRel.valuation _ _
          (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel)
        (@Whittaker.inverseStandardCharacter _ _
          (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n) := by
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  let := (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel
  have hint :=
    (RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero _ ψv hcond).1
  exact ⟨GeneralLinear.Iwasawa.isIntegrallyTrivial_standardCharacter hint n,
    GeneralLinear.Iwasawa.isIntegrallyTrivial_inverseStandardCharacter hint n⟩

/-! ### The local term -/

/-- The scalar by which left translation by `ι_v(ϖ_v^λ)` multiplies the kernel, times the
modulus factor `N(v)^(∑_(i<j)(λ_i-λ_j))`, is the local term of weight `λ`. -/
theorem absNorm_zpow_mul_eq_localTerm (v : FinitePlace F) {r t : ℕ} (h : t < r)
    {θ : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v) →* ℂˣ}
    {θ' : Langlands.GeneralLinear.upperUnipotent (t + 1) (FiniteCompletion F v) →* ℂˣ}
    (hθ : IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) θ)
    (hθ' : IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) θ')
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ) (s : ℂ) (lam : Fin (t + 1) → ℤ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
        (sphericalWhittaker (isUniformizingElement_canonical v) θ (residueCardinality v) a
            (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (torus (placeUniformizer v) lam)) *
          sphericalWhittaker (isUniformizingElement_canonical v) θ' (residueCardinality v) b
            (torus (placeUniformizer v) lam) *
          detPower F (t + 1) (localPoint F (t + 1) v (torus (placeUniformizer v) lam))
            (s - ((r - t : ℕ) : ℂ) / 2)) =
      localTerm (residueCardinality v) a b s lam := by
  rw [RankinSelberg.UnramifiedUnequalLocalSum.localTerm_eq_sphericalWhittaker
      (isUniformizingElement_canonical v) hθ hθ', padGL_torus, EqualEulerPointwise.modulusExponent_eq, detPower,
    detNorm_localPoint, log_norm_det_torus]
  have hq : (residueCardinality v : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast CuspidalPairEulerConvergence.residueCardinality_eq_absNorm v
  rw [hq, Real.log_zpow, Complex.ofReal_zpow]
  push_cast
  ring_nf

/-! ### One place -/

/-- `N_m(𝔸) g` has a representative `n g` with `n ∈ N_m(𝔸)`. -/
theorem exists_out_mk_eq {m : ℕ} (g : Points F m) :
    ∃ n ∈ unipotentAdelic F m, (LeftCosetSpace.mk (unipotentAdelic F m) g).out = n * g := by
  have hq : LeftCosetSpace.mk (unipotentAdelic F m)
      (LeftCosetSpace.mk (unipotentAdelic F m) g).out = LeftCosetSpace.mk (unipotentAdelic F m) g :=
    Quotient.out_eq _
  have hmem := inv_mem ((LeftCosetSpace.mk_eq_mk_iff _ _ _).1 hq)
  refine ⟨(LeftCosetSpace.mk (unipotentAdelic F m) g).out * g⁻¹, ?_, by group⟩
  simpa [mul_inv_rev] using hmem

open Classical in
/-- **One-place step.** Let `v ∉ A`, and let `W`, `W'` factor at `v` through the spherical
Whittaker functions `W°(·; a)`, `W°(·; b)` of integrally trivial characters, with left
`N_m(𝔸)`-invariant kernel. If the local terms of `a`, `b` sum to `L`, then adding `v` to `A`
multiplies the partial Whittaker integral by `L`. -/
theorem setIntegral_insert_eq_mul (hB : WhittakerCellDecompositionStatement.{u})
    {r t : ℕ} (h : t < r) {W : Points F (r + 1) → ℂ} {W' : Points F (t + 1) → ℂ} {s : ℂ}
    (hint : Integrable (unequalWhittakerIntegrand F h W W' s)
      (whittakerQuotientMeasure F (t + 1)))
    (hN : ∀ n ∈ unipotentAdelic F (t + 1), ∀ x,
      Unfolding.ordinaryKernel F h W W' s (n * x) = Unfolding.ordinaryKernel F h W W' s x)
    (A : Finset (FinitePlace F)) (v : FinitePlace F) (hvA : v ∉ A)
    {θ : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v) →* ℂˣ}
    {θ' : Langlands.GeneralLinear.upperUnipotent (t + 1) (FiniteCompletion F v) →* ℂˣ}
    (hθ : IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) θ)
    (hθ' : IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) θ')
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ)
    (hW : ∀ g : Points F (r + 1), finiteComponent F (r + 1) v g = 1 → ∀ k,
      W (g * localPoint F (r + 1) v k) =
        W g * sphericalWhittaker (isUniformizingElement_canonical v) θ (residueCardinality v) a k)
    (hW' : ∀ g : Points F (t + 1), finiteComponent F (t + 1) v g = 1 → ∀ k,
      W' (g * localPoint F (t + 1) v k) =
        W' g * sphericalWhittaker (isUniformizingElement_canonical v) θ' (residueCardinality v) b k)
    {L : ℂ} (hL : HasSum (localTerm (residueCardinality v) a b s) L) :
    ∫ q in unipotentIntegralClasses F (t + 1) (insert v A), unequalWhittakerIntegrand F h W W' s q
        ∂whittakerQuotientMeasure F (t + 1) =
      L * ∫ q in unipotentIntegralClasses F (t + 1) A, unequalWhittakerIntegrand F h W W' s q
        ∂whittakerQuotientMeasure F (t + 1) := by
  set f := unequalWhittakerIntegrand F h W W' s with hf
  set ϖ := placeUniformizer v
  set I := ∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1)
  have hϖ := isUniformizingElement_canonical v
  have hφ : ∀ x k, k ∈ FiniteAdelicGL.localIntegral F (r + 1) v →
      sphericalWhittaker hϖ θ (residueCardinality v) a (x * k) =
        sphericalWhittaker hϖ θ (residueCardinality v) a x := fun x k hk =>
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ a hθ x
      (mem_integralSubgroup_of_mem_localIntegral v hk)
  have hφ' : ∀ x k, k ∈ FiniteAdelicGL.localIntegral F (t + 1) v →
      sphericalWhittaker hϖ θ' (residueCardinality v) b (x * k) =
        sphericalWhittaker hϖ θ' (residueCardinality v) b x := fun x k hk =>
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ b hθ' x
      (mem_integralSubgroup_of_mem_localIntegral v hk)
  have hφ1 := GeneralLinear.Spherical.sphericalWhittaker_one hϖ (residueCardinality v) a hθ
  have hφ'1 := GeneralLinear.Spherical.sphericalWhittaker_one hϖ (residueCardinality v) b hθ'
  have hpt : ∀ lam, ∀ q ∈ unipotentIntegralClasses F (t + 1) A,
      f (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
          (localPoint F (t + 1) v (torus ϖ lam) * q.out)) =
        (sphericalWhittaker hϖ θ (residueCardinality v) a
            (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (torus ϖ lam)) *
          sphericalWhittaker hϖ θ' (residueCardinality v) b (torus ϖ lam) *
          detPower F (t + 1) (localPoint F (t + 1) v (torus ϖ lam))
            (s - ((r - t : ℕ) : ℂ) / 2)) * f q := by
    intro lam q hq
    have hq' : ∀ w ∉ A, IsUnipotentIntegral F (t + 1) w (finiteComponent F (t + 1) w q.out) :=
      hq
    obtain ⟨n, hn, e⟩ := exists_out_mk_eq (localPoint F (t + 1) v (torus ϖ lam) * q.out)
    rw [hf, Unfolding.unequalWhittakerIntegrand_eq, Unfolding.unequalWhittakerIntegrand_eq, e,
      hN n hn]
    exact ordinaryKernel_localPoint_mul h hW hW' hφ hφ' hφ1 hφ'1 s hN (torus ϖ lam)
      (fun u hu => isUnitriangular_torus_conj ϖ lam hu) (hq' v hvA)
  obtain ⟨-, hsum⟩ := hB F (t + 1) A v hvA ϖ (isUniformizingElement_valued v) f hint
  have hsum' : HasSum (fun lam => localTerm (residueCardinality v) a b s lam * I)
      (∫ q in unipotentIntegralClasses F (t + 1) (insert v A), f q
        ∂whittakerQuotientMeasure F (t + 1)) := by
    convert hsum using 1
    funext lam
    rw [setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) A) (hpt lam),
      integral_const_mul, ← mul_assoc, absNorm_zpow_mul_eq_localTerm v h hθ hθ' a b s lam]
  exact hsum'.unique (hL.mul_right I)

/-! ### The reduction -/

/-- **Reduction.** The unequal-rank partial Euler factorization follows from the unramified
factorization of global Whittaker functions, the one-place cell decomposition of the Whittaker
quotient measure, and the unfolding statement. -/
theorem unequalEulerFactorization_of_premises
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (hB : WhittakerCellDecompositionStatement.{u})
    (hU : UnequalUnfoldingStatement.{u}) :
    UnequalEulerFactorizationStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r t h T T' P P' S hP hP' hψS
  classical
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨C, -, hC⟩ := hU F r t h T T'
  obtain ⟨σ₁, hσ₁⟩ := exists_partialEulerFactor_convergence P P' hP hP'
  obtain ⟨A₀, hA₀⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨B₀, hB₀⟩ := exists_hasSatakeBound_presentation T' P'
  obtain ⟨σ₂, hσ₂⟩ := RankinSelberg.UnramifiedUnequalLocalSum.exists_hasSum_localTerm h A₀ B₀
  refine ⟨max C (max σ₁ σ₂), fun x x' hx hx' => ?_⟩
  intro W W' s hs
  have hsC : C < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs₁ : σ₁ < s.re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs₂ : σ₂ < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hint : Integrable (unequalWhittakerIntegrand F h W W' s)
      (whittakerQuotientMeasure F (t + 1)) :=
    ((hC ψ.complex hstd x x').1 s hsC).1
  obtain ⟨hsum, hprod⟩ := hσ₁ s hs₁
  refine ⟨hint, hsum, _, hprod, ?_⟩
  rw [unequalWhittakerIntegral, partialUnequalWhittakerIntegral_eq_setIntegral]
  rw [mul_comm]
  refine integral_eq_hasProd_mul_setIntegral hint hprod ?_
  intro A hSA v hv
  rw [Finset.cons_eq_insert]
  obtain ⟨ψv, hcan, hcond⟩ := hψS v.1 v.2
  obtain ⟨hθ, -⟩ := isIntegrallyTrivial_standardCharacters v.1 ψv hcond r
  obtain ⟨-, hθ'⟩ := isIntegrallyTrivial_standardCharacters v.1 ψv hcond t
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (P.spectralSystem.eigenvalues v.1 fun h' => v.2 (hP h'))
  obtain ⟨b, hb⟩ := Unramified.Eigenvalues.ofTuple_surjective (t + 1)
    (P'.spectralSystem.eigenvalues v.1 fun h' => v.2 (hP' h'))
  have hN : ∀ n ∈ unipotentAdelic F (t + 1), ∀ y,
      Unfolding.ordinaryKernel F h W W' s (n * y) = Unfolding.ordinaryKernel F h W W' s y :=
    fun n hn y =>
      Unfolding.ordinaryKernel_whittaker_unipotent_mul F h T T' ψ.complex hstd x x' s ⟨n, hn⟩ y
  have hW : ∀ g : Points F (r + 1), finiteComponent F (r + 1) v.1 g = 1 → ∀ k,
      W (g * localPoint F (r + 1) v.1 k) =
        W g * sphericalWhittaker (isUniformizingElement_canonical v.1)
          (@Whittaker.standardCharacter _ _
            (CompletionPadic.padicField v.1).canonicalTopologicalData.topology ψv r)
          (residueCardinality v.1) a k := fun g hg k =>
    (hA F ψ hψ r T P S hP hψS x hx v.1 v.2 ψv hcan (placeUniformizer v.1)
      (isUniformizingElement_canonical v.1) a ha g hg k).1
  have hW' : ∀ g : Points F (t + 1), finiteComponent F (t + 1) v.1 g = 1 → ∀ k,
      W' (g * localPoint F (t + 1) v.1 k) =
        W' g * sphericalWhittaker (isUniformizingElement_canonical v.1)
          (@Whittaker.inverseStandardCharacter _ _
            (CompletionPadic.padicField v.1).canonicalTopologicalData.topology ψv t)
          (residueCardinality v.1) b k := fun g hg k =>
    (hA F ψ hψ t T' P' S hP' hψS x' hx' v.1 v.2 ψv hcan (placeUniformizer v.1)
      (isUniformizingElement_canonical v.1) b hb g hg k).2
  have hmem : ∀ {n : ℕ} (z : Fin n → ℂˣ) (i : Fin n),
      z i ∈ ((Unramified.Eigenvalues.ofTuple z : Unramified.Eigenvalues n) : Multiset ℂˣ) := by
    intro n z i
    change z i ∈ ((List.ofFn z : List ℂˣ) : Multiset ℂˣ)
    rw [Multiset.mem_coe]
    simp
  have hq1 : 1 < residueCardinality v.1 :=
    lt_of_lt_of_le one_lt_two (CuspidalPairEulerConvergence.two_le_residueCardinality v.1)
  have hloc := (hσ₂ (residueCardinality v.1) hq1 a b
    (fun i => hA₀ v.1 (fun h' => v.2 (hP h')) (a i) (ha ▸ hmem a i))
    (fun j => hB₀ v.1 (fun h' => v.2 (hP' h')) (b j) (hb ▸ hmem b j)) s hs₂).2
  have hEF : partialEulerFactor P P' hP hP' v s =
      (∏ i : Fin (r + 1), ∏ j : Fin (t + 1),
        (1 - (a i : ℂ) * b j * (residueCardinality v.1 : ℂ) ^ (-s)))⁻¹ := by
    rw [partialEulerFactor, ← ha, ← hb, pairEulerPolynomial_ofTuple]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, RankinSelberg.spectralPoint]
  rw [hEF]
  exact setIntegral_insert_eq_mul hB h hint hN A v.1 hv hθ hθ' a b hW hW' hloc

end Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorization

namespace Langlands.Global.RankinSelbergGlobal

/-- **Reduction statement** for `UnequalEulerFactorizationStatement`: the factorization of
global Whittaker functions at an unramified place, the one-place cell decomposition of the
Whittaker quotient measure and the unfolding statement together imply the unequal-rank
partial Euler factorization. -/
def UnequalEulerFactorizationReductionStatement : Prop :=
  UnramifiedWhittakerFactorizationStatement.{u, uQ} →
    WhittakerCellDecompositionStatement.{u} →
      UnequalUnfoldingStatement.{u} → UnequalEulerFactorizationStatement.{u, uQ}

/-- Proof of the reduction statement. -/
theorem unequalEulerFactorizationReduction :
    UnequalEulerFactorizationReductionStatement.{u, uQ} :=
  fun hA hB hU => UnequalEulerFactorization.unequalEulerFactorization_of_premises hA hB hU

end Langlands.Global.RankinSelbergGlobal
