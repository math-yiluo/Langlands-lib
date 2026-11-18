import Langlands.Global.RankinSelberg.SelfPairLandau
import Langlands.Global.RankinSelberg.EqualEulerFactorizationReduction
import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition

/-! # Bounds on finite Euler products from partial Whittaker integrals

Write `Ψ_A(s) = ∫_(classes integral outside A) W W' Φ |det|^s` for finite sets `A` of finite
places. Suppose this integrand has a nonnegative Mellin weight, is integrable on `Re s > 1`,
and `Ψ_(S₁)(σ) > 0` at real `σ > 1`. Then the one-place Euler identities
`Ψ_(A ∪ {v}) = L(s, Π_v × Π'_v) Ψ_A`, proved by `EqualEulerReduction.setIntegral_insert` far to
the right, continue to `Re s > 1`. At real `σ > 1` they give
`‖∏_(v ∈ E) L(σ, Π_v × Π'_v)‖ ≤ Ψ(σ) / Ψ_(S₁)(σ)`. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SelfPairEulerBound

open CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation

local instance selfPairEulerBoundSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance selfPairEulerBoundSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### Continuation of finite Euler identities -/

section Abstract

variable {Idx : Type*} [DecidableEq Idx] {Ψ : Finset Idx → ℂ → ℂ} {L : Idx → ℂ → ℂ}

/-- One-place identities give the finite product identity on the same half-plane. -/
theorem eq_prod_of_insert {R : ℝ}
    (hins : ∀ (E : Finset Idx) (v : Idx), v ∉ E → ∀ s : ℂ, R < s.re →
      Ψ (insert v E) s = L v s * Ψ E s)
    (E : Finset Idx) {s : ℂ} (hs : R < s.re) : Ψ E s = (∏ v ∈ E, L v s) * Ψ ∅ s := by
  induction E using Finset.induction_on with
  | empty => simp
  | insert v E hv ih =>
    rw [hins E v hv s hs, ih, Finset.prod_insert hv]
    ring

/-- **Continuation of the finite product identity.** If the one-place identities hold on
`R < Re s` and all functions are holomorphic on `σ₀ < Re s`, the finite product identity
holds on `σ₀ < Re s`. -/
theorem eq_prod_of_insert_of_differentiableOn {σ₀ R : ℝ}
    (hΨ : ∀ E, DifferentiableOn ℂ (Ψ E) {s : ℂ | σ₀ < s.re})
    (hL : ∀ v, DifferentiableOn ℂ (L v) {s : ℂ | σ₀ < s.re})
    (hins : ∀ (E : Finset Idx) (v : Idx), v ∉ E → ∀ s : ℂ, R < s.re →
      Ψ (insert v E) s = L v s * Ψ E s)
    (E : Finset Idx) {s : ℂ} (hs : σ₀ < s.re) : Ψ E s = (∏ v ∈ E, L v s) * Ψ ∅ s := by
  have hg : DifferentiableOn ℂ (fun s => (∏ v ∈ E, L v s) * Ψ ∅ s) {s : ℂ | σ₀ < s.re} :=
    (DifferentiableOn.fun_finsetProd fun v _ => hL v).mul (hΨ ∅)
  exact LandauMellin.eqOn_halfPlane (hΨ E) hg (fun s hs => eq_prod_of_insert hins E hs) hs

omit [DecidableEq Idx] in
/-- The real-point bound: if `Ψ_E(σ) = (∏ L_v(σ)) Ψ_∅(σ)` with `Ψ_E(σ)` a real number in
`[0, B]` and `Ψ_∅(σ)` a positive real number, then `‖∏ L_v(σ)‖ ≤ B / Ψ_∅(σ)`. -/
theorem norm_prod_le {E : Finset Idx} {σ : ℂ}
    (heq : Ψ E σ = (∏ v ∈ E, L v σ) * Ψ ∅ σ) {a b B : ℝ} (ha : Ψ E σ = a) (hb : Ψ ∅ σ = b)
    (ha0 : 0 ≤ a) (haB : a ≤ B) (hb0 : 0 < b) : ‖∏ v ∈ E, L v σ‖ ≤ B / b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hprod : ∏ v ∈ E, L v σ = (a : ℂ) / b := by
    rw [ha, hb] at heq
    rw [heq, mul_div_assoc, div_self hb', mul_one]
  rw [hprod, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_pos hb0]
  exact div_le_div_of_nonneg_right haB hb0.le

end Abstract

/-! ### Holomorphy of the local factors on `Re s > 1` -/

section Local

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : Automorphic.CuspidalOperatorRealization F r}

omit [CompactSpace (AdeleQuotient F)] in
/-- If all Satake parameters at `v` have norm at most `q_v ^ (1/2)`, the pair Euler polynomial
does not vanish at `q_v ^ (-s)` for `Re s > 1`. -/
theorem eval_ne_zero {n m : ℕ} (a : Unramified.Eigenvalues n) (b : Unramified.Eigenvalues m)
    (v : FinitePlace F)
    (ha : ∀ α ∈ (a : Multiset ℂˣ), ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hb : ∀ β ∈ (b : Multiset ℂˣ), ‖(β : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    {s : ℂ} (hs : 1 < s.re) :
    (pairEulerPolynomial a b).eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠
      0 := by
  have hq2 : (2 : ℝ) ≤ residueCardinality v := by
    exact_mod_cast CuspidalPairEulerConvergence.two_le_residueCardinality v
  have hq : (0 : ℝ) < residueCardinality v := by linarith
  rw [CuspidalPairEulerConvergence.eval_pairEulerPolynomial]
  intro h0
  rw [Multiset.prod_eq_zero_iff] at h0
  obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h0
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
  rw [Multiset.mem_product] at hz
  have hlt : ‖(z.1 : ℂ) * z.2 * RankinSelberg.spectralPoint (residueCardinality v) s‖ < 1 := by
    rw [norm_mul, norm_mul, CuspidalPairEulerConvergence.norm_spectralPoint]
    calc ‖(z.1 : ℂ)‖ * ‖(z.2 : ℂ)‖ * (residueCardinality v : ℝ) ^ (-s.re)
        ≤ Real.sqrt (residueCardinality v : ℝ) * Real.sqrt (residueCardinality v : ℝ) *
            (residueCardinality v : ℝ) ^ (-s.re) := by
          gcongr
          · exact ha _ hz.1
          · exact hb _ hz.2
      _ = (residueCardinality v : ℝ) ^ (1 - s.re) := by
          rw [Real.mul_self_sqrt hq.le, show (1 : ℝ) - s.re = 1 + -s.re by ring,
            Real.rpow_add hq, Real.rpow_one]
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have h1 : (z.1 : ℂ) * z.2 * RankinSelberg.spectralPoint (residueCardinality v) s = 1 := by
    linear_combination -hw0
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- Under the bounds `q_v ^ (1/2)` on the Satake parameters, every local factor
`L(s, Π_v × Π'_v)` outside `S` is holomorphic on `Re s > 1`. -/
theorem differentiableOn_partialEulerFactor
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hP'b : ∀ v (hv : v ∉ S), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (v : {v : FinitePlace F // v ∉ S}) :
    DifferentiableOn ℂ (partialEulerFactor P P' hP hP' v) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hq : 0 < residueCardinality v.1 := by
    have := CuspidalPairEulerConvergence.two_le_residueCardinality v.1
    omega
  have hne := eval_ne_zero _ _ v.1 (hPb v.1 v.2) (hP'b v.1 v.2) (s := s) hs
  set p := pairEulerPolynomial (P.spectralSystem.eigenvalues v.1 fun h => v.2 (hP h))
    (P'.spectralSystem.eigenvalues v.1 fun h => v.2 (hP' h)) with hp
  have hd : Differentiable ℂ
      (fun w => p.eval (RankinSelberg.spectralPoint (residueCardinality v.1) w)) :=
    (Polynomial.differentiable p).comp (EqualSemilocalReduction.differentiable_spectralPoint hq)
  have he : partialEulerFactor P P' hP hP' v =
      fun w => (p.eval (RankinSelberg.spectralPoint (residueCardinality v.1) w))⁻¹ := rfl
  rw [he]
  exact ((hd s).inv hne).differentiableWithinAt

end Local

/-! ### The partial Whittaker integrals -/

section Whittaker

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The places outside `S₁` as finite places. -/
def placeEmb (S₁ : Finset (FinitePlace F)) : {v : FinitePlace F // v ∉ S₁} ↪ FinitePlace F :=
  Function.Embedding.subtype _

omit [NumberField F] [CompactSpace (AdeleQuotient F)] in
theorem union_insert_eq_cons [DecidableEq (FinitePlace F)] (S₁ : Finset (FinitePlace F))
    (E : Finset {v : FinitePlace F // v ∉ S₁}) (v : {v : FinitePlace F // v ∉ S₁})
    (hvA : v.1 ∉ S₁ ∪ E.map (placeEmb S₁)) :
    S₁ ∪ (insert v E).map (placeEmb S₁) = Finset.cons v.1 (S₁ ∪ E.map (placeEmb S₁)) hvA := by
  ext w
  simp only [Finset.mem_union, Finset.mem_map, Finset.mem_insert, Finset.mem_cons, placeEmb,
    Function.Embedding.subtype_apply]
  constructor
  · rintro (h | ⟨x, hx | hx, rfl⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (by rw [hx])
    · exact Or.inr (Or.inr ⟨x, hx, rfl⟩)
  · rintro (rfl | h | ⟨x, hx, rfl⟩)
    · exact Or.inr ⟨v, Or.inl rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, Or.inr hx, rfl⟩

omit [NumberField F] [CompactSpace (AdeleQuotient F)] in
theorem not_mem_union_map [DecidableEq (FinitePlace F)] (S₁ : Finset (FinitePlace F))
    (E : Finset {v : FinitePlace F // v ∉ S₁}) (v : {v : FinitePlace F // v ∉ S₁})
    (hvE : v ∉ E) : v.1 ∉ S₁ ∪ E.map (placeEmb S₁) := by
  rw [Finset.mem_union, Finset.mem_map]
  rintro (h | ⟨x, hx, hxv⟩)
  · exact v.2 h
  · have : x = v := Subtype.ext hxv
    exact hvE (this ▸ hx)

/-- **Bounded finite Euler products from the partial Whittaker integrals.** Assume:

* the hypotheses of the one-place Euler step `EqualEulerReduction.setIntegral_insert` at
  `S₁`;
* the bounds `q_v ^ (1/2)` on both spectra outside `S₁`;
* a nonnegative Mellin weight `f` for the global integrand, which is integrable on
  `Re s > 1`;
* positivity at every real `σ > 1` of the partial integral over the classes integral outside
  `S₁`.

Then at every real `σ > 1` the finite partial products of `L(σ, Π_v × Π'_v)` over places
outside `S₁` are bounded. -/
theorem prod_bound
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
    {S₁ : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S₁) (hP' : P'.exceptional ⊆ S₁)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S₁)
    {C C' : ℝ} (hC : HasSatakeBound P C)
    (hC' : HasSatakeBound P' C')
    (hPb : ∀ v (hv : v ∉ S₁), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hP'b : ∀ v (hv : v ∉ S₁), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    {x : T.Space} (hx : IsSphericalOutside F T S₁ x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S₁ x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S₁ Φ)
    {f : WhittakerQuotient F (r + 1) → ℝ}
    (hG : SelfPairLandau.IsMellin (equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
      (cuspWhittaker F T' ψ.complex⁻¹ x') Φ) f)
    (hf : ∀ q, 0 ≤ f q)
    (hint : ∀ s : ℂ, 1 < s.re →
      Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s) (whittakerQuotientMeasure F (r + 1)))
    (hpos : ∀ σ : ℝ, 1 < σ →
      0 < ∫ q in unipotentIntegralClasses F (r + 1) S₁,
        f q * Real.exp (σ * SelfPairLandau.logDet (r + 1) q) ∂whittakerQuotientMeasure F (r + 1))
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ M : ℝ, ∀ E : Finset {v : FinitePlace F // v ∉ S₁},
      ‖∏ v ∈ E, partialEulerFactor P P' hP hP' v σ‖ ≤ M := by
  classical
  set ν := whittakerQuotientMeasure F (r + 1) with hν
  set G := equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
    (cuspWhittaker F T' ψ.complex⁻¹ x') Φ with hGdef
  let Ψ : Finset {v : FinitePlace F // v ∉ S₁} → ℂ → ℂ := fun E s =>
    ∫ q in unipotentIntegralClasses F (r + 1) (S₁ ∪ E.map (placeEmb S₁)), G s q ∂ν
  have hΨ : ∀ E, DifferentiableOn ℂ (Ψ E) {s : ℂ | 1 < s.re} := fun E =>
    hG.differentiableOn_setIntegral hf hint _
  have hL : ∀ v, DifferentiableOn ℂ (partialEulerFactor P P' hP hP' v) {s : ℂ | 1 < s.re} :=
    differentiableOn_partialEulerFactor P P' hP hP' hPb hP'b
  have hins : ∀ (E : Finset {v : FinitePlace F // v ∉ S₁}) (v : {v : FinitePlace F // v ∉ S₁}),
      v ∉ E → ∀ s : ℂ, max (EqualEulerLocal.localRadius r C C') 1 < s.re →
        Ψ (insert v E) s = partialEulerFactor P P' hP hP' v s * Ψ E s := by
    intro E v hvE s hs
    have hvA := not_mem_union_map S₁ E v hvE
    show ∫ q in unipotentIntegralClasses F (r + 1) (S₁ ∪ (insert v E).map (placeEmb S₁)),
        G s q ∂ν = _
    rw [union_insert_eq_cons S₁ E v hvA]
    exact EqualEulerReduction.setIntegral_insert UnramifiedWhittaker.unramifiedWhittakerFactorization
      whittakerCellDecomposition ψ hψ hP hP' hψS hC hC' hx hx' hΦ
      (lt_of_le_of_lt (le_max_left _ _) hs) (hint s (lt_of_le_of_lt (le_max_right _ _) hs))
      Finset.subset_union_left v hvA
  have heq := fun E => eq_prod_of_insert_of_differentiableOn hΨ hL hins E
    (s := (σ : ℂ)) (by rw [Complex.ofReal_re]; exact hσ)
  have hreal : Integrable (fun q => f q * Real.exp (σ * SelfPairLandau.logDet (r + 1) q)) ν :=
    hG.integrable_real hf (hint σ (by rw [Complex.ofReal_re]; exact hσ))
  set b := ∫ q in unipotentIntegralClasses F (r + 1) S₁,
    f q * Real.exp (σ * SelfPairLandau.logDet (r + 1) q) ∂ν with hbdef
  set B := ∫ q, f q * Real.exp (σ * SelfPairLandau.logDet (r + 1) q) ∂ν with hBdef
  refine ⟨B / b, fun E => ?_⟩
  refine norm_prod_le (heq E) (hG.setIntegral_real _ σ) ?_
    (SelfPairLandau.setIntegral_real_nonneg hf _ σ) ?_ (hpos σ hσ)
  · show Ψ ∅ σ = (b : ℂ)
    simp only [Ψ, Finset.map_empty, Finset.union_empty]
    exact hG.setIntegral_real _ σ
  · have h := SelfPairLandau.setIntegral_real_mono (ν := ν) hf
      (Set.subset_univ (unipotentIntegralClasses F (r + 1) (S₁ ∪ E.map (placeEmb S₁)))) hreal
    rwa [Measure.restrict_univ] at h

/-- `prod_bound` with the positivity hypothesis taken at one real point: it suffices that the
partial integral `Ψ_(S₁∪∞)` has positive real part at a single real `σ₀ > 1`. -/
theorem prod_bound_of_re_pos
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
    {S₁ : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S₁) (hP' : P'.exceptional ⊆ S₁)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S₁)
    {C C' : ℝ} (hC : HasSatakeBound P C)
    (hC' : HasSatakeBound P' C')
    (hPb : ∀ v (hv : v ∉ S₁), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hP'b : ∀ v (hv : v ∉ S₁), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    {x : T.Space} (hx : IsSphericalOutside F T S₁ x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S₁ x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S₁ Φ)
    {f : WhittakerQuotient F (r + 1) → ℝ}
    (hG : SelfPairLandau.IsMellin (equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
      (cuspWhittaker F T' ψ.complex⁻¹ x') Φ) f)
    (hf : ∀ q, 0 ≤ f q)
    (hint : ∀ s : ℂ, 1 < s.re →
      Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s) (whittakerQuotientMeasure F (r + 1)))
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    (hpos : 0 < (partialEqualWhittakerIntegral F S₁ (cuspWhittaker F T ψ.complex x)
      (cuspWhittaker F T' ψ.complex⁻¹ x') Φ σ₀).re)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ M : ℝ, ∀ E : Finset {v : FinitePlace F // v ∉ S₁},
      ‖∏ v ∈ E, partialEulerFactor P P' hP hP' v σ‖ ≤ M :=
  prod_bound ψ hψ hP hP' hψS hC hC' hPb hP'b hx hx' hΦ hG hf hint
    (fun σ' hσ' => SelfPairLandau.setIntegral_real_pos_of_re_pos hG hf
      (hint σ₀ (by rw [Complex.ofReal_re]; exact hσ₀))
      (hint σ' (by rw [Complex.ofReal_re]; exact hσ')) hpos) hσ

end Whittaker

end Langlands.Global.RankinSelbergGlobal.SelfPairEulerBound
