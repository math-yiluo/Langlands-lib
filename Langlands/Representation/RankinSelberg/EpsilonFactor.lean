import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Classification.Supercuspidal

/-!
# Epsilon factors of pairs as relations on JPSS functional equations

`IsPairEpsilonFactor` says that the nonzero monomial `c q^(-ms)` is the
epsilon factor in the functional equation of JPSS 1983 Theorem 2.7(iii) for
every compatible quotient measure and every pair of nonzero Whittaker
functionals. No factor function is chosen and existence is not assumed.
Uniqueness and invariance under equivalence are proved.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uG uV uW uV₂ uW₂

section Monomials

/-- Two unit multiples of integer powers agreeing on an infinite set of nonzero
points have the same coefficient and exponent. -/
theorem unitMonomial_eq_of_infinite {c c' : ℂˣ} {m m' : ℤ} {U : Set ℂ}
    (hU : U.Infinite) (h0 : ∀ x ∈ U, x ≠ 0)
    (h : ∀ x ∈ U, (c : ℂ) * x ^ m = (c' : ℂ) * x ^ m') : c = c' ∧ m = m' := by
  set N : ℕ := m.natAbs + m'.natAbs
  have ha : 0 ≤ m + N := by omega
  have hb : 0 ≤ m' + N := by omega
  have hpoly : C (c : ℂ) * X ^ (m + N).toNat = C (c' : ℂ) * X ^ (m' + N).toNat := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hU.mono
    intro x hx
    have hx0 := h0 x hx
    have e1 : x ^ (m + N).toNat = x ^ m * x ^ (N : ℤ) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg ha, zpow_add₀ hx0]
    have e2 : x ^ (m' + N).toNat = x ^ m' * x ^ (N : ℤ) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hb, zpow_add₀ hx0]
    change eval x (C (c : ℂ) * X ^ (m + N).toNat) = eval x (C (c' : ℂ) * X ^ (m' + N).toNat)
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [e1, e2, ← mul_assoc, ← mul_assoc, h x hx]
  have hdeg : (m + N).toNat = (m' + N).toNat := by
    have hd := congrArg Polynomial.natDegree hpoly
    rwa [natDegree_C_mul_X_pow _ _ c.ne_zero, natDegree_C_mul_X_pow _ _ c'.ne_zero] at hd
  have hm : m = m' := by omega
  refine ⟨?_, hm⟩
  rw [hdeg] at hpoly
  have hC := mul_right_cancel₀ (pow_ne_zero _ X_ne_zero) hpoly
  exact Units.ext (C_inj.mp hC)

/-- The spectral point `q^(-s)` is nonzero for a positive cardinality. -/
theorem spectralPoint_ne_zero {q : ℕ} (hq : 1 < q) (s : ℂ) : spectralPoint q s ≠ 0 := by
  intro h
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- A nonzero polynomial vanishes at the spectral points of only finitely many
real parameters. -/
theorem finite_spectralPoint_roots {q : ℕ} (hq : 1 < q) {P : ℂ[X]} (hP : P ≠ 0) :
    {t : ℝ | P.eval (spectralPoint q t) = 0}.Finite := by
  apply ((P.roots.toFinset.finite_toSet).preimage
    (spectralPoint_ofReal_injective hq).injOn).subset
  intro t ht
  change spectralPoint q t ∈ (P.roots.toFinset : Set ℂ)
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP]
  exact ht

/-- The same finiteness for the reflected spectral points `q^(-(1-s))`. -/
theorem finite_reflected_spectralPoint_roots {q : ℕ} (hq : 1 < q) {P : ℂ[X]}
    (hP : P ≠ 0) : {t : ℝ | P.eval (spectralPoint q (1 - (t : ℂ))) = 0}.Finite := by
  have hinj : Function.Injective (fun t : ℝ => 1 - t) := fun a b h => by
    simpa using h
  apply ((finite_spectralPoint_roots hq hP).preimage hinj.injOn).subset
  intro t ht
  change P.eval (spectralPoint q (1 - (t : ℂ))) = 0 at ht
  change P.eval (spectralPoint q ((1 - t : ℝ) : ℂ)) = 0
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using ht

/-- A normalized generator of a value set forces a nonzero value. -/
theorem IsNormalizedGenerator.exists_ne_zero {values : Set RationalFunctions} {P : ℂ[X]}
    (h : IsNormalizedGenerator values P) : ∃ R ∈ values, R ≠ 0 := by
  by_contra! hzero
  have hspan : zetaSpan values = ⊥ := (Submodule.span_eq_bot).mpr hzero
  have hmem : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan values := by
    rw [h.2]
    exact Submodule.mem_span_singleton_self _
  rw [hspan, Submodule.mem_bot, inv_eq_zero] at hmem
  exact h.polynomial_ne_zero
    ((map_eq_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mp hmem)

/-- The epsilon monomial of a normalized functional equation is unique once the
generator and one continuation are nonzero. -/
theorem NormalizedFunctionalEquation.epsilon_unique {q : ℕ} (hq : 1 < q)
    {P Pdual : ℂ[X]} {ζ c c' : ℂˣ} {e : ℕ} {m m' : ℤ} {R Rdual : RationalFunctions}
    (hP : P ≠ 0) (hR : R ≠ 0)
    (h : NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual)
    (h' : NormalizedFunctionalEquation q P Pdual ζ c' e m' R Rdual) :
    c = c' ∧ m = m' := by
  have hnum : R.num ≠ 0 := RatFunc.num_ne_zero hR
  set bad : Set ℝ :=
    {t | R.denom.eval (spectralPoint q t) = 0} ∪ {t | R.num.eval (spectralPoint q t) = 0} ∪
      {t | P.eval (spectralPoint q t) = 0} ∪
      {t | Rdual.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} with hbad_def
  have hbad : bad.Finite :=
    (((finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
      (finite_spectralPoint_roots hq hnum)).union (finite_spectralPoint_roots hq hP)).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rdual))
  have hU : ((fun t : ℝ => spectralPoint q t) '' badᶜ).Infinite :=
    hbad.infinite_compl.image (spectralPoint_ofReal_injective hq).injOn
  apply unitMonomial_eq_of_infinite hU
  · rintro x ⟨t, -, rfl⟩
    exact spectralPoint_ne_zero hq _
  · rintro x ⟨t, ht, rfl⟩
    simp only [hbad_def, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    obtain ⟨⟨⟨hden, hnum0⟩, hP0⟩, hdual⟩ := ht
    have h1 := h t hden hdual
    have h2 := h' t hden hdual
    have hReval : RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) R ≠ 0 := by
      simpa only [RatFunc.eval, eval₂_id] using div_ne_zero hnum0 hden
    have hne : (ζ : ℂ) ^ e * (P.eval (spectralPoint q t) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) R) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ζ.ne_zero) (mul_ne_zero hP0 hReval)
    have h12 := h1.symm.trans h2
    unfold epsilonMonomial at h12
    apply mul_right_cancel₀ hne
    calc (c : ℂ) * spectralPoint q t ^ m * ((ζ : ℂ) ^ e * (P.eval (spectralPoint q t) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) R))
        = (ζ : ℂ) ^ e * ((c : ℂ) * spectralPoint q t ^ m) * (P.eval (spectralPoint q t) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) R) := by ring
      _ = (ζ : ℂ) ^ e * ((c' : ℂ) * spectralPoint q t ^ m') * (P.eval (spectralPoint q t) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) R) := h12
      _ = _ := by ring

end Monomials

section ModelTransport

variable {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {π : Representation ℂ G V} {π₂ : Representation ℂ G V₂}

/-- Pull back an equivariant functional along an actual representation equivalence. -/
def functionalPullback (φ : π.Equiv π₂) (ℓ : functionals N θ π₂) : functionals N θ π :=
  ⟨ℓ.val ∘ₗ φ.toLinearMap, fun u v => by
    have hφ : φ (π (u : G) v) = π₂ (u : G) (φ v) :=
      Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (u : G) v
    change ℓ.val (φ (π (u : G) v)) = (θ u : ℂ) * ℓ.val (φ v)
    rw [hφ]
    exact ℓ.property u (φ v)⟩

@[simp] theorem functionalPullback_apply (φ : π.Equiv π₂) (ℓ : functionals N θ π₂) (v : V) :
    (functionalPullback φ ℓ).val v = ℓ.val (φ v) := rfl

theorem functionalPullback_ne_zero (φ : π.Equiv π₂) {ℓ : functionals N θ π₂}
    (hℓ : ℓ.val ≠ 0) : (functionalPullback φ ℓ).val ≠ 0 := by
  intro h0
  apply hℓ
  ext w
  have hw := congrArg (fun f : Module.Dual ℂ V => f (φ.symm w)) h0
  simpa only [functionalPullback_apply, φ.apply_symm_apply, LinearMap.zero_apply] using hw

theorem coefficientMap_functionalPullback (φ : π.Equiv π₂) (ℓ : functionals N θ π₂)
    (v : V) : coefficientMap π (functionalPullback φ ℓ) v = coefficientMap π₂ ℓ (φ v) := by
  apply Subtype.ext
  funext g
  have hφ : φ (π g v) = π₂ g (φ v) := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v
  change ℓ.val (φ (π g v)) = ℓ.val (π₂ g (φ v))
  rw [hφ]

/-- Equivalent representations have the same coefficient image for corresponding
functionals. -/
theorem coefficientModel_functionalPullback (φ : π.Equiv π₂) (ℓ : functionals N θ π₂) :
    coefficientModel π (functionalPullback φ ℓ) = coefficientModel π₂ ℓ := by
  apply Subrepresentation.toSubmodule_injective
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨φ v, (coefficientMap_functionalPullback φ ℓ v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨φ.symm v, ?_⟩
    change coefficientMap π (functionalPullback φ ℓ) (φ.symm v) = coefficientMap π₂ ℓ v
    rw [coefficientMap_functionalPullback, φ.apply_symm_apply]

end ModelTransport


section EqualRankEquation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

/-- The equal-rank functional equation of JPSS Theorem 2.7(iii) for the specified
functionals and quotient measure, with the epsilon monomial `c q^(-ms)` fixed.
The body is that of `EqualRankFunctionalEquationConclusion` with `c` and `m`
moved out of the existential. -/
def EqualRankEpsilonEquation (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (c : ℂˣ) (m : ℤ) : Prop :=
  ∃ (ζ : ℂˣ) (P Pdual : Polynomial ℂ),
    HasModelMinusOneScalar σ ℓ' ζ ∧
    IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P ∧
    IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') Pdual ∧
    ∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
    ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ (Φhat : SchwartzBruhat (Fin (n + 1) → F)) (R Rdual : RationalFunctions),
        IsRowFourierPair ψ ν Φ Φhat ∧
        HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R ∧
        HasRationalContinuation q
          (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat) Rdual ∧
        NormalizedFunctionalEquation q P Pdual ζ c n m R Rdual

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The published functional-equation conclusion is the existence of some
epsilon monomial satisfying the fixed-monomial equation. -/
theorem exists_equalRankEpsilonEquation_iff :
    (∃ (c : ℂˣ) (m : ℤ), EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m) ↔
      EqualRankFunctionalEquationConclusion q ψ abv μ ν π σ ℓ ℓ' := by
  constructor
  · rintro ⟨c, m, ζ, P, Pdual, h⟩
    exact ⟨ζ, c, m, P, Pdual, h⟩
  · rintro ⟨ζ, c, m, P, Pdual, h⟩
    exact ⟨c, m, ζ, P, Pdual, h⟩

/-- The equation depends on the functionals only through their coefficient models. -/
theorem EqualRankEpsilonEquation.congr_model {ℓ₂ : glFunctionals ψ n π₂}
    {ℓ₂' : glInverseFunctionals ψ n σ₂} {c : ℂˣ} {m : ℤ}
    (hM : coefficientModel π ℓ = coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' = coefficientModel σ₂ ℓ₂') :
    EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m ↔
      EqualRankEpsilonEquation q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' c m := by
  unfold EqualRankEpsilonEquation HasModelMinusOneScalar equalRankRationalValues
    dualEqualRankRationalValues equalRankModelIntegral dualEqualRankModelIntegral
  rw [hM, hM']

/-- For a nonzero second functional and `q > 1`, the epsilon monomial of the
fixed-functional equation is unique. -/
theorem EqualRankEpsilonEquation.unique (hq : 1 < q) (hℓ' : ℓ'.val ≠ 0)
    {c c' : ℂˣ} {m m' : ℤ}
    (h : EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m)
    (h' : EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c' m') :
    c = c' ∧ m = m' := by
  obtain ⟨ζ, P, Pdual, hζ, hP, hPd, hFE⟩ := h
  obtain ⟨ζ', P', Pdual', hζ', hP', hPd', hFE'⟩ := h'
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ hζ'
  obtain rfl := hP.unique hP'
  obtain rfl := hPd.unique hPd'
  obtain ⟨R, ⟨f, f', Φ, hR⟩, hR0⟩ := hP.exists_ne_zero
  obtain ⟨Φhat, R₁, Rd₁, hΦ₁, hR₁, hRd₁, hN₁⟩ := hFE f f' Φ
  obtain ⟨Φhat', R₂, Rd₂, hΦ₂, hR₂, hRd₂, hN₂⟩ := hFE' f f' Φ
  obtain rfl := hΦ₁.unique hΦ₂
  obtain rfl := hR.unique hq hR₁
  obtain rfl := hR.unique hq hR₂
  obtain rfl := hRd₁.unique hq hRd₂
  exact NormalizedFunctionalEquation.epsilon_unique hq hP.polynomial_ne_zero hR0 hN₁ hN₂

/-- Pulling both functionals back along representation equivalences does not
change the equation. -/
theorem EqualRankEpsilonEquation.functionalPullback_iff (φ : π.Equiv π₂)
    (φ' : σ.Equiv σ₂) (ℓ₂ : glFunctionals ψ n π₂) (ℓ₂' : glInverseFunctionals ψ n σ₂)
    {c : ℂˣ} {m : ℤ} :
    EqualRankEpsilonEquation q ψ abv μ ν π σ (functionalPullback φ ℓ₂)
        (functionalPullback φ' ℓ₂') c m ↔
      EqualRankEpsilonEquation q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' c m :=
  EqualRankEpsilonEquation.congr_model (coefficientModel_functionalPullback φ ℓ₂)
    (coefficientModel_functionalPullback φ' ℓ₂')

end EqualRankEquation

section UnequalRankEquation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

omit [IsTopologicalRing F] in
/-- The published fixed-rank value set, written without the rank transport. -/
theorem unequalRankValuesAt_eq (j k : ℕ) (hr : r = n + (j + k + 1)) (q : ℕ)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ' =
      {R | ∃ f : (coefficientModel π ℓ).toSubmodule,
        ∃ f' : (coefficientModel σ ℓ').toSubmodule,
          HasRationalContinuation q (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val) R} := by
  subst hr
  rfl

/-- The unequal-rank functional equation of JPSS Theorem 2.7(iii) for the
specified functionals and quotient measure, with the epsilon monomial fixed.
The body is that of `UnequalRankFunctionalEquationConclusion` with `c` and `m`
moved out of the existential; it still covers every block `j`. -/
def UnequalRankEpsilonEquation (hnr : n < r)
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (c : ℂˣ) (m : ℤ) : Prop :=
  ∃ (ζ : ℂˣ) (P Pdual : Polynomial ℂ),
    HasModelMinusOneScalar σ ℓ' ζ ∧
    ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
          π σ ℓ ℓ') P ∧
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ ℓ ℓ') Pdual ∧
      ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∃ R Rdual : RationalFunctions,
          HasRationalContinuation q
            (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
              f.val f'.val) R ∧
          HasRationalContinuation q
            (dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ' f f') Rdual ∧
          NormalizedFunctionalEquation q P Pdual ζ c r m R Rdual

variable {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The published functional-equation conclusion is the existence of some
epsilon monomial satisfying the fixed-monomial equation. -/
theorem exists_unequalRankEpsilonEquation_iff :
    (∃ (c : ℂˣ) (m : ℤ), UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m) ↔
      UnequalRankFunctionalEquationConclusion hnr q ψ abv μ ν π σ ℓ ℓ' := by
  constructor
  · rintro ⟨c, m, ζ, P, Pdual, h⟩
    exact ⟨ζ, c, m, P, Pdual, h⟩
  · rintro ⟨ζ, c, m, P, Pdual, h⟩
    exact ⟨c, m, ζ, P, Pdual, h⟩

/-- The equation depends on the functionals only through their coefficient models. -/
theorem UnequalRankEpsilonEquation.congr_model {ℓ₂ : glFunctionals ψ r π₂}
    {ℓ₂' : glInverseFunctionals ψ n σ₂} {c : ℂˣ} {m : ℤ}
    (hM : coefficientModel π ℓ = coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' = coefficientModel σ₂ ℓ₂') :
    UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m ↔
      UnequalRankEpsilonEquation hnr q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' c m := by
  unfold UnequalRankEpsilonEquation
  simp only [unequalRankValuesAt_eq]
  unfold HasModelMinusOneScalar dualUnequalRankRationalValuesAt dualUnequalRankModelIntegralAt
  rw [hM, hM']

/-- For a nonzero second functional and `q > 1`, the epsilon monomial of the
fixed-functional equation is unique; the block `j = 0` already determines it. -/
theorem UnequalRankEpsilonEquation.unique (hq : 1 < q) (hℓ' : ℓ'.val ≠ 0)
    {c c' : ℂˣ} {m m' : ℤ}
    (h : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m)
    (h' : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c' m') :
    c = c' ∧ m = m' := by
  obtain ⟨ζ, P, Pdual, hζ, hall⟩ := h
  obtain ⟨ζ', P', Pdual', hζ', hall'⟩ := h'
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ hζ'
  have hr : r = n + (0 + (r - n - 1) + 1) := by omega
  obtain ⟨hP, hPd, hFE⟩ := hall 0 (r - n - 1) hr
  obtain ⟨hP', hPd', hFE'⟩ := hall' 0 (r - n - 1) hr
  obtain rfl := hP.unique hP'
  obtain rfl := hPd.unique hPd'
  obtain ⟨R, hRmem, hR0⟩ := hP.exists_ne_zero
  rw [unequalRankValuesAt_eq] at hRmem
  obtain ⟨f, f', hR⟩ := hRmem
  obtain ⟨R₁, Rd₁, hR₁, hRd₁, hN₁⟩ := hFE f f'
  obtain ⟨R₂, Rd₂, hR₂, hRd₂, hN₂⟩ := hFE' f f'
  obtain rfl := hR.unique hq hR₁
  obtain rfl := hR.unique hq hR₂
  obtain rfl := hRd₁.unique hq hRd₂
  exact NormalizedFunctionalEquation.epsilon_unique hq hP.polynomial_ne_zero hR0 hN₁ hN₂

/-- Pulling both functionals back along representation equivalences does not
change the equation. -/
theorem UnequalRankEpsilonEquation.functionalPullback_iff (φ : π.Equiv π₂)
    (φ' : σ.Equiv σ₂) (ℓ₂ : glFunctionals ψ r π₂) (ℓ₂' : glInverseFunctionals ψ n σ₂)
    {c : ℂˣ} {m : ℤ} :
    UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ (functionalPullback φ ℓ₂)
        (functionalPullback φ' ℓ₂') c m ↔
      UnequalRankEpsilonEquation hnr q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' c m :=
  UnequalRankEpsilonEquation.congr_model (coefficientModel_functionalPullback φ ℓ₂)
    (coefficientModel_functionalPullback φ' ℓ₂')

end UnequalRankEquation

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]

/-- `e = (c, m)` is the epsilon factor `c q^(-ms)` of the equal-rank pair
`(π, σ)`. A compatible quotient measure and nonzero functionals for both
representations exist, and the fixed-monomial functional equation holds for
every compatible quotient measure and every pair of nonzero functionals. -/
def IsEqualRankEpsilonFactor (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (e : ℂˣ × ℤ) : Prop :=
  (∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n)) ∧
  (∃ ℓ : glFunctionals ψ n π, ℓ.val ≠ 0) ∧
  (∃ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0) ∧
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' e.1 e.2

/-- `e = (c, m)` is the epsilon factor of the pair `(π, σ)` of ranks
`r + 1 > n + 1`, in the same sense as `IsEqualRankEpsilonFactor`. Only the
quotient measure of the smaller rank occurs. -/
def IsUnequalRankEpsilonFactor (hnr : n < r) (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (e : ℂˣ × ℤ) : Prop :=
  (∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n)) ∧
  (∃ ℓ : glFunctionals ψ r π, ℓ.val ≠ 0) ∧
  (∃ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0) ∧
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' e.1 e.2

/-- The epsilon-factor relation for a candidate `π` of rank `r + 1` and a test
`σ` of rank `n + 1`. It is the unequal-rank relation when `n < r`, the
equal-rank relation when `r = n`, and false when the test rank is larger. -/
def IsPairEpsilonFactor (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (e : ℂˣ × ℤ) : Prop :=
  if hnr : n < r then IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e
  else if hrn : r = n then
    IsEqualRankEpsilonFactor (n := n) q ψ abv ν (hrn ▸ π) σ e
  else False

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {e e' : ℂˣ × ℤ}

section EqualRank

variable {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

/-- The equal-rank epsilon factor is unique when `q > 1`. -/
theorem IsEqualRankEpsilonFactor.unique (hq : 1 < q)
    (h : IsEqualRankEpsilonFactor q ψ abv ν π σ e)
    (h' : IsEqualRankEpsilonFactor q ψ abv ν π σ e') : e = e' := by
  obtain ⟨⟨hinv, μ, hμ⟩, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  obtain ⟨-, -, -, hall'⟩ := h'
  obtain ⟨h1, h2⟩ := (@hall hinv μ hμ ℓ ℓ' hℓ hℓ').unique hq hℓ' (@hall' hinv μ hμ ℓ ℓ' hℓ hℓ')
  exact Prod.ext h1 h2

/-- The equal-rank relation transfers along representation equivalences. -/
theorem IsEqualRankEpsilonFactor.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : IsEqualRankEpsilonFactor q ψ abv ν π σ e) :
    IsEqualRankEpsilonFactor q ψ abv ν π₂ σ₂ e := by
  obtain ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  refine ⟨hμ, ⟨functionalPullback φ.symm ℓ, functionalPullback_ne_zero φ.symm hℓ⟩,
    ⟨functionalPullback φ'.symm ℓ', functionalPullback_ne_zero φ'.symm hℓ'⟩, ?_⟩
  intro hinv μ hμc ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  exact (EqualRankEpsilonEquation.functionalPullback_iff φ φ' ℓ₂ ℓ₂').mp
    (@hall hinv μ hμc _ _ (functionalPullback_ne_zero φ hℓ₂)
      (functionalPullback_ne_zero φ' hℓ₂'))

/-- The equal-rank relation is invariant under representation equivalences. -/
theorem IsEqualRankEpsilonFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsEqualRankEpsilonFactor q ψ abv ν π σ e ↔ IsEqualRankEpsilonFactor q ψ abv ν π₂ σ₂ e :=
  ⟨IsEqualRankEpsilonFactor.of_equiv φ φ', IsEqualRankEpsilonFactor.of_equiv φ.symm φ'.symm⟩

end EqualRank

section UnequalRank

variable {hnr : n < r} {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

/-- The unequal-rank epsilon factor is unique when `q > 1`. -/
theorem IsUnequalRankEpsilonFactor.unique (hq : 1 < q)
    (h : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e)
    (h' : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e') : e = e' := by
  obtain ⟨⟨hinv, μ, hμ⟩, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  obtain ⟨-, -, -, hall'⟩ := h'
  obtain ⟨h1, h2⟩ := (@hall hinv μ hμ ℓ ℓ' hℓ hℓ').unique hq hℓ' (@hall' hinv μ hμ ℓ ℓ' hℓ hℓ')
  exact Prod.ext h1 h2

/-- The unequal-rank relation transfers along representation equivalences. -/
theorem IsUnequalRankEpsilonFactor.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e) :
    IsUnequalRankEpsilonFactor hnr q ψ abv ν π₂ σ₂ e := by
  obtain ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  refine ⟨hμ, ⟨functionalPullback φ.symm ℓ, functionalPullback_ne_zero φ.symm hℓ⟩,
    ⟨functionalPullback φ'.symm ℓ', functionalPullback_ne_zero φ'.symm hℓ'⟩, ?_⟩
  intro hinv μ hμc ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  exact (UnequalRankEpsilonEquation.functionalPullback_iff φ φ' ℓ₂ ℓ₂').mp
    (@hall hinv μ hμc _ _ (functionalPullback_ne_zero φ hℓ₂)
      (functionalPullback_ne_zero φ' hℓ₂'))

/-- The unequal-rank relation is invariant under representation equivalences. -/
theorem IsUnequalRankEpsilonFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e ↔
      IsUnequalRankEpsilonFactor hnr q ψ abv ν π₂ σ₂ e :=
  ⟨IsUnequalRankEpsilonFactor.of_equiv φ φ', IsUnequalRankEpsilonFactor.of_equiv φ.symm φ'.symm⟩

end UnequalRank

section Pair

variable {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}

theorem isPairEpsilonFactor_of_lt (hnr : n < r) :
    IsPairEpsilonFactor q ψ abv ν π σ e ↔ IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e := by
  rw [IsPairEpsilonFactor, dite_eq_left hnr]

theorem isPairEpsilonFactor_self {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} :
    IsPairEpsilonFactor q ψ abv ν π σ e ↔ IsEqualRankEpsilonFactor q ψ abv ν π σ e := by
  rw [IsPairEpsilonFactor, dite_eq_right (lt_irrefl n), dite_eq_left rfl]

/-- There is no epsilon factor when the test rank exceeds the candidate rank. -/
theorem not_isPairEpsilonFactor_of_lt (hrn : r < n) : ¬ IsPairEpsilonFactor q ψ abv ν π σ e := by
  rw [IsPairEpsilonFactor, dite_eq_right (by omega), dite_eq_right (by omega)]
  exact id

/-- The pair epsilon factor is unique when `q > 1`. -/
theorem IsPairEpsilonFactor.unique (hq : 1 < q) (h : IsPairEpsilonFactor q ψ abv ν π σ e)
    (h' : IsPairEpsilonFactor q ψ abv ν π σ e') : e = e' := by
  by_cases hnr : n < r
  · rw [isPairEpsilonFactor_of_lt hnr] at h h'
    exact h.unique hq h'
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairEpsilonFactor_self] at h h'
      exact h.unique hq h'
    · exact absurd h (not_isPairEpsilonFactor_of_lt (by omega))

/-- The pair relation transfers along representation equivalences. -/
theorem IsPairEpsilonFactor.of_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (h : IsPairEpsilonFactor q ψ abv ν π σ e) : IsPairEpsilonFactor q ψ abv ν π₂ σ₂ e := by
  by_cases hnr : n < r
  · rw [isPairEpsilonFactor_of_lt hnr] at h ⊢
    exact h.of_equiv φ φ'
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairEpsilonFactor_self] at h ⊢
      exact h.of_equiv φ φ'
    · exact absurd h (not_isPairEpsilonFactor_of_lt (by omega))

/-- The pair relation is invariant under representation equivalences. -/
theorem IsPairEpsilonFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsPairEpsilonFactor q ψ abv ν π σ e ↔ IsPairEpsilonFactor q ψ abv ν π₂ σ₂ e :=
  ⟨IsPairEpsilonFactor.of_equiv φ φ', IsPairEpsilonFactor.of_equiv φ.symm φ'.symm⟩

end Pair

end Relations

section Classes

variable {p : ℕ} [Fact p.Prime]

/-- The epsilon-factor relation on supercuspidal isomorphism classes of a
p-adic field with its canonical topological data: `q` is the residue
cardinality and the absolute value is the normalized one. The candidate class
`π` has rank `r + 1` and the test class `τ` has rank `n + 1`. -/
def IsClassEpsilonFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} (π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r))
    (τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n))
    (e : ℂˣ × ℤ) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  Quotient.lift₂
    (fun (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
        (B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)) =>
      IsPairEpsilonFactor F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) ν
        A.obj.representation B.obj.representation e)
    (by
      rintro A B A' B' ⟨i⟩ ⟨j⟩
      exact propext (IsPairEpsilonFactor.congr_equiv
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso i))
        (SmoothRep.equivOfIso (GeneralLinear.supercuspidalProperty.ι.mapIso j))))
    π τ

/-- On representatives the class relation is the pair relation. -/
theorem isClassEpsilonFactor_mk (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) {r n : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
    (B : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1))
    (e : ℂˣ × ℤ) :
    IsClassEpsilonFactor F ψ ν (Quotient.mk _ A) (Quotient.mk _ B) e ↔
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := borel F.Carrier
      letI : BorelSpace F.Carrier := ⟨rfl⟩
      letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F.Carrier)
      letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      IsPairEpsilonFactor F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) ν
        A.obj.representation B.obj.representation e :=
  Iff.rfl

/-- The class-level epsilon factor is unique. -/
theorem IsClassEpsilonFactor.unique {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier} {r n : ℕ}
    {π : PadicField.SupercuspidalClass.{uV, uF} F (r + 1) (Nat.succ_pos r)}
    {τ : PadicField.SupercuspidalClass.{uW, uF} F (n + 1) (Nat.succ_pos n)}
    {e e' : ℂˣ × ℤ} (h : IsClassEpsilonFactor F ψ ν π τ e)
    (h' : IsClassEpsilonFactor F ψ ν π τ e') : e = e' := by
  revert h h'
  refine Quotient.inductionOn₂ π τ ?_
  intro A B h h'
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact IsPairEpsilonFactor.unique
    (PadicField.TopologicalData.residueCardinality_gt_one _) h h'

end Classes

end Langlands.RankinSelberg
