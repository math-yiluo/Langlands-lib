import Langlands.Global.Factors.CuspidalPairCompletedEquationReduction
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonProof
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalLocalGenericityStatement

/-!
# Reduction of the cuspidal-pair continuation to the partial equation with integral gammas

`CuspidalPairPartialGammaEquationStatement` is the partial functional equation of
Cogdell (2004), proof of Theorem 4.1 (p.220): the partial completed L-functions
`Λ^S = L_∞ L^S` of a cuspidal pair and of the contragredient pair continue
meromorphically, and `Λ^S(s) = (∏_(v ∈ S) γ_v(s)) ε_∞(s) Λ^S∨(1 - s)` with the integral
(Jacquet–Piatetski-Shapiro–Shalika) gamma factors `γ_v` of the actual local components at
the finite places of `S`. As in `CuspidalPairContinuationStatement`, the partial
L-functions are identified with the Euler products only where these converge.

`cuspidalPairPartialGammaReduction` proves that it implies
`CuspidalPairContinuationStatement`. The finite comparison of the classification factors
of `FinitePairFactorChoice` with the integral gamma factors, and the passage from the
partial to the completed L-functions, are proved here from the Library. With
`cuspidalPairCompletedEquationReduction`, the Satake bound and the partial equation imply
`CuspidalPairCompletedEquationStatement`. See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Automorphic.CuspidalPairPartialGamma

open Langlands.Global

/-- **Local genericity** of the actual local components of cuspidal spectral
presentations, without a central-character hypothesis: a proof of the published
`CuspidalLocalGenericityStatement`. The proof is that of
`cuspidalUnitaryLocalGenericity`, which does not use its unitary hypothesis. -/
theorem localGenericity : CuspidalLocalGenericityStatement.{u, uQ} := by
  intro F _ _ _ r T P v hI hA
  have hne : CuspidalWhittaker.localCharacter F v ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := CuspidalWhittaker.exists_localCharacter_ne_one F v
    exact ht (by rw [h, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional (P.localComponent v)
    (P.localComponent_isCuspidal v) (P.localComponent_ne_bot v)
  exact (P.localComponent v).isGeneric_of_integerTrivial_character hI hA
    (CuspidalWhittaker.localCharacter F v) hne
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one F hx) ℓ hℓ heq

end Langlands.Automorphic.CuspidalPairPartialGamma

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing
open LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

namespace CuspidalPairPartialGamma

/-- Removing finitely many nonzero factors from a convergent product of complex numbers:
the remaining product converges to the value divided by the removed factors. -/
theorem hasProd_subtype_notMem {ι : Type*} {S : Finset ι} {f : ι → ℂ} {p : ℂ}
    (hf : HasProd f p) (hS : ∀ i ∈ S, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ S} => f i) (p * ∏ i ∈ S, (f i)⁻¹) := by
  classical
  let g : ι → ℂ := fun i => if i ∈ S then (f i)⁻¹ else 1
  have hg : HasProd g (∏ i ∈ S, (f i)⁻¹) := by
    have h0 : HasProd g (∏ i ∈ S, g i) :=
      hasProd_prod_of_ne_finset_one (fun i hi => by simp [g, hi])
    rwa [Finset.prod_congr rfl (fun i hi => by simp [g, hi] : ∀ i ∈ S, g i = (f i)⁻¹)] at h0
  have hfg := hf.mul hg
  have key : (fun i : {i // i ∉ S} => f i) = (fun i => f i * g i) ∘ Subtype.val := by
    funext i
    simp [g, i.2]
  rw [key, Subtype.val_injective.hasProd_iff]
  · exact hfg
  · intro i hi
    have hiS : i ∈ S := by
      by_contra hn
      exact hi ⟨⟨i, hn⟩, rfl⟩
    simp [g, hiS, hS i hiS]

/-- If a product `∏_i f_i = p` converges and `Λ = L · p^S` whenever the product `p^S` of
the factors outside the finite set `S` converges, then `(∏_(i ∈ S) f_i) Λ = L · p`. -/
theorem prod_mul_eq_of_hasProd {ι : Type*} {S : Finset ι} {f : ι → ℂ}
    (g : {i // i ∉ S} → ℂ) (hfg : ∀ i : {i // i ∉ S}, f i = g i) {Λ L : ℂ}
    (hΛ : ∀ p, HasProd g p → Λ = L * p) {p : ℂ} (hp : HasProd f p) :
    (∏ i ∈ S, f i) * Λ = L * p := by
  by_cases hz : ∀ i ∈ S, f i ≠ 0
  · have h1 := hasProd_subtype_notMem hp hz
    rw [show (fun i : {i // i ∉ S} => f i) = g from funext hfg] at h1
    rw [hΛ _ h1]
    have hone : (∏ i ∈ S, f i) * ∏ i ∈ S, (f i)⁻¹ = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i hi => mul_inv_cancel₀ (hz i hi))
    calc (∏ i ∈ S, f i) * (L * (p * ∏ i ∈ S, (f i)⁻¹))
        = L * p * ((∏ i ∈ S, f i) * ∏ i ∈ S, (f i)⁻¹) := by ring
      _ = L * p := by rw [hone, mul_one]
  · push Not at hz
    obtain ⟨i, hi, h0⟩ := hz
    have hp0 : p = 0 := hp.unique (hasProd_zero_of_exists_eq_zero ⟨i, h0⟩)
    rw [Finset.prod_eq_zero hi h0, hp0]
    ring

end CuspidalPairPartialGamma

/-- **Partial functional equation with integral gamma factors** (Cogdell 2004, proof of
Theorem 4.1, p.220), without convergence. In the situation of
`CuspidalPairContinuationStatement`, with `S` containing the four exceptional sets and
the finite ramification of `ψ`: there are a real `σ` and functions `Λ`, `Λd`, meromorphic
on `ℂ`, such that

* for `Re s > σ`, whenever the Euler product `∏_(v ∉ S) L(s, Π_v × Π'_v)` of the
  unramified factors converges to `p`, `Λ(s) = L_∞(s) p`; likewise
  `Λd(s) = L∨_∞(s) pd` for the contragredient pair;
* for every family of components `ψ_v` of `ψ`, self-dual measures `ν_v` and integral
  gamma factors `G_v` of the actual local components at the places `v ∈ S`, off a
  discrete set `Λ(s) = (∏_(v ∈ S) G_v(q_v^(-s))) ε_∞(s) Λd(1 - s)`. -/
def CuspidalPairPartialGammaEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∃ x : Adeles F, ψ x ≠ 1) → (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r t : ℕ) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (_hd : HasIrreducibleAdmissibleComponents Pd)
    (_hd' : HasIrreducibleAdmissibleComponents Pd')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  ∃ (σ : ℝ) (Λ Λd : ℂ → ℂ),
    MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λd Set.univ ∧
    (∀ s : ℂ, σ < s.re → ∀ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p → Λ s = infiniteL s * p) ∧
    (∀ s : ℂ, σ < s.re → ∀ pd : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) pd →
        Λd s = dualInfiniteL s * pd) ∧
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
      (∀ v ∈ S,
        letI := (padicField v).canonicalTopologicalData.topology
        letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v).canonicalGeneralLinearTopology (t + 1)
        RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
          ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
          ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (G v)) →
    ∀ᶠ s in Filter.codiscrete ℂ,
      Λ s = (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
        infiniteEpsilon s * Λd (1 - s)

/-- The partial equation with integral gamma factors implies the continuation statement
of cuspidal pairs. -/
def CuspidalPairPartialGammaReductionStatement : Prop :=
  CuspidalPairPartialGammaEquationStatement.{u, uQ} →
    CuspidalPairContinuationStatement.{u, uQ}

namespace CuspidalPairFunctionalEquation.FinitePairFactorChoice

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {r t : ℕ} {T Td : CuspidalOperatorRealization F r}
  {T' Td' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T}
  {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
  {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
  (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')

omit [CompactSpace (AdeleQuotient F)] in
theorem one_lt_residueCardinality (v : FinitePlace F) : 1 < residueCardinality v :=
  (padicField v).canonicalTopologicalData.residueCardinality_gt_one

/-- `s ↦ L(s, Π_v × Π'_v)` is meromorphic on `ℂ`. -/
theorem meromorphicOn_finiteL (v : FinitePlace F) :
    MeromorphicOn (fun s => c.finiteL v s) Set.univ := fun s _ =>
  (RankinSelberg.analyticAt_polynomial_spectralPoint _ (one_lt_residueCardinality v)
    (c.lPolynomial v) s).meromorphicAt.inv

/-- `s ↦ L(s, Π∨_v × Π'∨_v)` is meromorphic on `ℂ`. -/
theorem meromorphicOn_finiteDualL (v : FinitePlace F) :
    MeromorphicOn (fun s => c.finiteDualL v s) Set.univ := fun s _ =>
  (RankinSelberg.analyticAt_polynomial_spectralPoint _ (one_lt_residueCardinality v)
    (c.dualLPolynomial v) s).meromorphicAt.inv

/-- The local class of `Pd` at `v` is the smooth dual of the local class of `P`. -/
theorem isSmoothDual_localClass
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
    (v : FinitePlace F) :
    Correspondence.IsSmoothDual (padicField v) (localClass P h v) (localClass Pd hd v) := by
  obtain ⟨E⟩ := Automorphic.cuspidalContragredientLocalCompatibility.{u, uQ, uQ}
    F r T Td hTd P Pd v (h v).1 (h v).2 (hd v).1 (hd v).2
  exact ⟨(P.localComponent v).padicObject (h v).1 (h v).2,
    (Pd.localComponent v).padicObject (hd v).1 (hd v).2, rfl, rfl, ⟨E.symm⟩⟩

/-- The gamma expression of the classification factors of `c` at `v` is the integral
gamma factor of the actual local components. -/
theorem isPadicSymmetricGammaFactor
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)
    (v : FinitePlace F) :
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
    letI := (padicField v).canonicalGeneralLinearTopology (t + 1)
    RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (c.additive v) (c.measure v)
      ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
      ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation
      (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection (padicField v))
        (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v)) := by
  have hcomp := Correspondence.hasGenericAutomorphicGammaComparison.{u, u}
    (F := padicField v) RankinSelberg.genericLanglandsPairEpsilonFactorComparison.{u, u, u}
  exact hcomp (c.additive v) ⟨c.measure v, c.measure_spec v⟩ r t
    ((P.localComponent v).padicObject (h v).1 (h v).2)
    ((P'.localComponent v).padicObject (h' v).1 (h' v).2)
    (Automorphic.CuspidalPairPartialGamma.localGenericity.{u, uQ} F r T P v (h v).1 (h v).2
      (c.additive v))
    (Automorphic.CuspidalPairPartialGamma.localGenericity.{u, uQ} F t T' P' v (h' v).1 (h' v).2
      (c.additive v))
    _ ⟨localClass Pd hd v, localClass Pd' hd' v, c.lPolynomial v, c.dualLPolynomial v,
      c.epsilon v, isSmoothDual_localClass hTd h hd v, isSmoothDual_localClass hTd' h' hd' v,
      c.lPolynomial_spec v, c.dualLPolynomial_spec v, c.epsilon_spec v, rfl⟩

/-- `L(s, Π_v × Π'_v) γ_v(s) = ε(s, Π_v × Π'_v, ψ_v) L(1 - s, Π∨_v × Π'∨_v)` off a discrete
set, for the gamma expression `γ_v` of the classification factors of `c`. -/
theorem eventually_finiteL_mul_gamma (v : FinitePlace F) :
    ∀ᶠ s in Filter.codiscrete ℂ,
      c.finiteL v s * RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s)
          (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection (padicField v))
            (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v)) =
        c.finiteEpsilon v s * c.finiteDualL v (1 - s) := by
  have hq := one_lt_residueCardinality v
  have hP : c.lPolynomial v ≠ 0 := (c.lPolynomial_spec v).ne_zero
  have hPd : c.dualLPolynomial v ≠ 0 := (c.dualLPolynomial_spec v).ne_zero
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  filter_upwards [RankinSelberg.polynomial_spectralPoint_eventually_ne_zero _ hq _ hP x,
    RankinSelberg.polynomial_reflected_spectralPoint_eventually_ne_zero _ hq _ hPd x]
    with s h1 h2
  have hz := RankinSelberg.spectralPoint_ne_zero hq s
  have hrefl : ((LocalFactor.residueReflection (padicField v) : ℂˣ) : ℂ) /
      RankinSelberg.spectralPoint (residueCardinality v) s =
        RankinSelberg.spectralPoint (residueCardinality v) (1 - s) := by
    rw [LocalFactor.coe_residueReflection, RankinSelberg.spectralPoint_one_sub hq s]
  rw [RankinSelberg.eval_rationalGammaExpression _ _ _ _ _ hz (by rw [hrefl]; exact h2), hrefl]
  simp only [finiteL, finiteDualL, finiteEpsilon]
  field_simp

/-- The partial equation with integral gamma factors gives the continuation statement
for `c`: `Λ(s) = (∏_(v ∈ S) L(s, Π_v × Π'_v)) Λ^S(s)` and likewise for `Λd`. -/
theorem continuationHolds_of_partialGamma {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (hPd' : Pd'.exceptional ⊆ S) (hc : c.IsUnramifiedOutside S)
    {Linf Ldinf εinf : ℂ → ℂ} {σ : ℝ} {Λ Λd : ℂ → ℂ}
    (hΛ : MeromorphicOn Λ Set.univ) (hΛd : MeromorphicOn Λd Set.univ)
    (hprod : ∀ s : ℂ, σ < s.re → ∀ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p → Λ s = Linf s * p)
    (hprodd : ∀ s : ℂ, σ < s.re → ∀ pd : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) pd → Λd s = Ldinf s * pd)
    (G : FinitePlace F → ℂ → ℂ)
    (hfe : ∀ᶠ s in Filter.codiscrete ℂ, Λ s = (∏ v ∈ S, G v s) * εinf s * Λd (1 - s))
    (hG : ∀ v ∈ S, ∀ᶠ s in Filter.codiscrete ℂ,
      c.finiteL v s * G v s = c.finiteEpsilon v s * c.finiteDualL v (1 - s)) :
    c.ContinuationHolds S Linf Ldinf εinf := by
  classical
  refine ⟨σ, fun s => (∏ v ∈ S, c.finiteL v s) * Λ s,
    fun s => (∏ v ∈ S, c.finiteDualL v s) * Λd s, ?_, ?_, ?_, ?_⟩
  · exact (MeromorphicOn.fun_prod fun v _ => c.meromorphicOn_finiteL v).mul hΛ
  · exact (MeromorphicOn.fun_prod fun v _ => c.meromorphicOn_finiteDualL v).mul hΛd
  · intro s hs p pd hp hpd
    constructor
    · refine CuspidalPairPartialGamma.prod_mul_eq_of_hasProd
        (fun v => partialEulerFactor P P' hP hP' v s) (fun v => ?_) (hprod s hs) hp
      simp only [finiteL, partialEulerFactor]
      rw [(hc v.1 v.2).1 (fun hm => v.2 (hP hm)) (fun hm => v.2 (hP' hm))]
    · refine CuspidalPairPartialGamma.prod_mul_eq_of_hasProd
        (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) (fun v => ?_) (hprodd s hs) hpd
      simp only [finiteDualL, partialEulerFactor]
      rw [(hc v.1 v.2).2.1 (fun hm => v.2 (hPd hm)) (fun hm => v.2 (hPd' hm))]
  · have hG' : ∀ᶠ s in Filter.codiscrete ℂ, ∀ v ∈ S,
        c.finiteL v s * G v s = c.finiteEpsilon v s * c.finiteDualL v (1 - s) :=
      (Filter.eventually_all_finset S).mpr hG
    filter_upwards [hfe, hG'] with s h1 h2
    rw [h1]
    calc (∏ v ∈ S, c.finiteL v s) * ((∏ v ∈ S, G v s) * εinf s * Λd (1 - s))
        = (∏ v ∈ S, (c.finiteL v s * G v s)) * εinf s * Λd (1 - s) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ = (∏ v ∈ S, (c.finiteEpsilon v s * c.finiteDualL v (1 - s))) * εinf s *
            Λd (1 - s) := by
          rw [Finset.prod_congr rfl h2]
      _ = (∏ v ∈ S, c.finiteEpsilon v s) * εinf s *
            ((∏ v ∈ S, c.finiteDualL v (1 - s)) * Λd (1 - s)) := by
          rw [Finset.prod_mul_distrib]
          ring

end CuspidalPairFunctionalEquation.FinitePairFactorChoice

/-- The reduction: the partial equation with integral gamma factors implies the
continuation statement of cuspidal pairs. -/
theorem cuspidalPairPartialGammaReduction :
    CuspidalPairPartialGammaReductionStatement.{u, uQ} := by
  intro hG F _ _ _ ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd' S hP
    hP' hPd hPd' hsupp c hc aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd'
    hdC hdC' hdCd hdCd'
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hprod, hprodd, hfe⟩ := hG F ψ hψ hdiag r t T Td T' Td' hTd hTd'
    P P' Pd Pd' h h' hd hd' S hP hP' hPd hPd' hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR'
    hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  exact c.continuationHolds_of_partialGamma hP hP' hPd hPd' hc hΛ hΛd hprod hprodd
    (fun v s => RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint (residueCardinality v) s)
      (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection (padicField v))
        (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v)))
    (hfe c.additive c.additive_spec c.measure c.measure_spec _
      (fun v _ => c.isPadicSymmetricGammaFactor hTd hTd' v))
    (fun v _ => c.eventually_finiteL_mul_gamma v)

/-- The Satake bound and the partial equation with integral gamma factors imply the
completed equation of cuspidal pairs for every admissible exceptional set. -/
theorem cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma
    (hSat : CuspidalSatakeBoundStatement.{u, uQ})
    (hG : CuspidalPairPartialGammaEquationStatement.{u, uQ}) :
    CuspidalPairCompletedEquationStatement.{u, uQ} :=
  cuspidalPairCompletedEquationReduction hSat (cuspidalPairPartialGammaReduction hG)

end Langlands.Global
