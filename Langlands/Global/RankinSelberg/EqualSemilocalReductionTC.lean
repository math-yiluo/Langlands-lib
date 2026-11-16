import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Global.RankinSelberg.SemilocalEquationTCStatements

/-! # Totally complex form of the equal-rank semi-local reduction

`EqualSemilocalFactorizationTCStatement` is the premise `EqualSemilocalFactorizationStatement`
with the instance argument `[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`,
at the same universe levels, the rest verbatim. `equalSemilocalReductionTC` proves that it
implies `EqualSemilocalEquationTCStatement`, by the proof of `equalSemilocalReduction`, which
uses the premise only at the field of the conclusion. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory Filter Topology
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalSemilocalReductionTCSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalSemilocalReductionTCSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Totally complex form of the premise** `EqualSemilocalFactorizationStatement` (Cogdell
2004, pp.219–220, with Theorem 3.2, p.214, and §3.2, pp.216–217): the same proposition with
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, the rest verbatim. Over a
totally complex field there is no real place, so the real-place products in `infiniteL`,
`dualInfiniteL` and `infiniteEpsilon` are empty products. -/
def EqualSemilocalFactorizationTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (hI : HasIrreducibleAdmissibleComponents P) (hI' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)), P.exceptional ⊆ S → P'.exceptional ⊆ S →
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter Td'.realization v
      (dCd' v)) →
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
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
    (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
  ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
    (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
  ∃ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
    IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
    Φ ∈ schwartzBruhat F (r + 1) ∧ IsStandardOutside F (r + 1) S Φ ∧
    let W := cuspWhittaker F T ψ.complex x
    let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
    let Wdual := dualFunction F (r + 1) W
    let W'dual := dualFunction F (r + 1) W'
    let Φhat := fourierTransform F (r + 1) ψ.complex Φ
    ∃ (σ : ℝ) (Z Zd : ℂ → ℂ) (κ : ℂ),
      MeromorphicOn Z Set.univ ∧ MeromorphicOn Zd Set.univ ∧
      (∀ᶠ s in Filter.codiscrete ℂ, Z s ≠ 0) ∧ (∀ᶠ s in Filter.codiscrete ℂ, Zd s ≠ 0) ∧
      (∀ᶠ s in Filter.codiscrete ℂ,
        infiniteL s * Zd (1 - s) = κ * infiniteEpsilon s * dualInfiniteL (1 - s) * Z s) ∧
      ∃ D : ∀ v : S,
          letI := (padicField v.1).canonicalTopologicalData.topology
          letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
          EqualLocalTestData (padicField v.1) (ψv v.1) (νv v.1)
            ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
            ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation,
        (∀ v (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).integral s ≠ 0) ∧
        (∀ v (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).dualIntegral s ≠ 0) ∧
        (∀ ζ : S → ℂˣ, (∀ v, (D v).HasMinusOneScalar (ζ v)) →
          κ * ∏ v, (ζ v : ℂ) ^ r = 1) ∧
        (∀ s : ℂ, σ < s.re →
          partialEqualWhittakerIntegral F S W W' Φ s = Z s * ∏ v, (D v).integral s) ∧
        ∀ s : ℂ, σ < s.re →
          partialEqualWhittakerIntegral F S Wdual W'dual Φhat s =
            Zd s * ∏ v, (D v).dualIntegral s

/-- The general premise implies its totally complex form, by forgetting the instance. -/
theorem equalSemilocalFactorizationTCStatement_of_general
    (h : EqualSemilocalFactorizationStatement.{u, uQ}) :
    EqualSemilocalFactorizationTCStatement.{u, uQ} :=
  fun F _ _ _ _ => h F

/-- The totally complex conditional reduction: the premise `EqualSemilocalFactorizationTCStatement`
implies the totally complex semi-local functional equation `EqualSemilocalEquationTCStatement`. -/
def EqualSemilocalReductionTCStatement : Prop :=
  EqualSemilocalFactorizationTCStatement.{u, uQ} → EqualSemilocalEquationTCStatement.{u, uQ}

/-- Two canonical finite components of `ψ` at the same place agree. -/
private theorem canonicalComponent_unique_tc {F : Type u} [Field F] [NumberField F]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {v : FinitePlace F}
    {ψv ψv' : Correspondence.NontrivialAdditiveCharacter (padicField v)}
    (h : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h' : IsCanonicalFiniteAdditiveComponent ψ v ψv') : ψv = ψv' := by
  rcases ψv with ⟨χ, hc, hn⟩
  rcases ψv' with ⟨χ', hc', hn'⟩
  have hχ : χ = χ' := DFunLike.ext χ χ' fun x => (h x).trans (h' x).symm
  subst hχ
  rfl

private theorem one_lt_residueCardinality_tc {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) : 1 < (padicField v).canonicalTopologicalData.residueCardinality := by
  have h : 2 ≤ (padicField v).canonicalTopologicalData.residueCardinality :=
    Langlands.Global.CuspidalPairEulerConvergence.two_le_residueCardinality v
  omega

open EqualSemilocalReduction in
/-- **The totally complex conditional reduction**: the proof of `equalSemilocalReduction`, with
the extra instance argument. -/
theorem equalSemilocalReductionTC : EqualSemilocalReductionTCStatement.{u, uQ} := by
  intro hfac F _ _ _ _ ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp
    aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    infiniteL dualInfiniteL infiniteEpsilon
  classical
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : ∀ v : FinitePlace F,
      Correspondence.NontrivialAdditiveCharacter (padicField v),
      ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψ0 v) :=
    ⟨canonicalFiniteAdditiveComponent ψ hdiag,
      isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hdiag⟩
  obtain ⟨ν0, hν0⟩ : ∃ ν0 : ∀ v : FinitePlace F,
      Correspondence.LocalAdditiveHaarMeasure (padicField v),
      ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψ0 v) (ν0 v) :=
    ⟨fun v => Correspondence.localSelfDualHaar (padicField v) (ψ0 v),
      fun v => Correspondence.isSelfDual_localSelfDualHaar (padicField v) (ψ0 v)⟩
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, hrest⟩ :=
    hfac F ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψ0 hψ0 ν0 hν0
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, ?_⟩
  intro W W' Wdual W'dual Φhat
  obtain ⟨σ, Z, Zd, κ, hZ, hZd, hZ0, hZd0, harch, D, hDne, hDdne, hsign, hfacA, hfacB⟩ :=
    hrest
  have harch' : ∀ᶠ s in codiscrete ℂ,
      infiniteL s * Zd (1 - s) = κ * infiniteEpsilon s * dualInfiniteL (1 - s) * Z s := harch
  -- residue cardinalities
  let q : S → ℕ := fun v => (padicField v.1).canonicalTopologicalData.residueCardinality
  have hq : ∀ v : S, 1 < q v := fun v => one_lt_residueCardinality_tc v.1
  -- rational continuations of the local integrals (JPSS Theorem 2.7)
  have hcont := fun v : S =>
    letI := (padicField v.1).canonicalTopologicalData.topology
    letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
    (D v).exists_continuations
    ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).property.1
    ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).property.2
    ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).property.1
    ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).property.2
  choose R hR using fun v => (hcont v).1
  choose Rd hRd using fun v => (hcont v).2
  have hRa : ∀ v : S, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      (D v).integral s = RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v) :=
    fun v => by
      obtain ⟨a, ha⟩ := hR v
      exact ⟨a, fun s hs => (ha s hs).2⟩
  have hRda : ∀ v : S, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      (D v).dualIntegral s =
        RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (Rd v) :=
    fun v => by
      obtain ⟨a, ha⟩ := hRd v
      exact ⟨a, fun s hs => (ha s hs).2⟩
  choose a ha using hRa
  choose ad had using hRda
  obtain ⟨M, hM⟩ := Finite.exists_le (fun v : S => max (a v) (ad v))
  -- the continuations are nonzero
  have hR0 : ∀ v, R v ≠ 0 := by
    intro v h0
    obtain ⟨s, hs, hne⟩ := hDne v (a v)
    exact hne (by rw [ha v s hs, h0, RatFunc.eval_zero])
  have hRd0 : ∀ v, Rd v ≠ 0 := by
    intro v h0
    obtain ⟨s, hs, hne⟩ := hDdne v (ad v)
    exact hne (by rw [had v s hs, h0, RatFunc.eval_zero])
  refine ⟨max σ M,
    fun s => Z s * ∏ v, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v),
    fun s => Zd s * ∏ v, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (Rd v),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hZ.mul (MeromorphicOn.fun_prod fun v _ => meromorphicOn_ratEval (by
      have := hq v; omega) (R v))
  · exact hZd.mul (MeromorphicOn.fun_prod fun v _ => meromorphicOn_ratEval (by
      have := hq v; omega) (Rd v))
  · intro s hs
    have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    refine Eq.trans ?_ (hfacA s hσ).symm
    show Z s * _ = Z s * _
    congr 1
    refine Finset.prod_congr rfl fun v _ => (ha v s ?_).symm
    exact lt_of_le_of_lt ((le_max_left _ _).trans (hM v))
      (lt_of_le_of_lt (le_max_right _ _) hs)
  · intro s hs
    have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    refine Eq.trans ?_ (hfacB s hσ).symm
    show Zd s * _ = Zd s * _
    congr 1
    refine Finset.prod_congr rfl fun v _ => (had v s ?_).symm
    exact lt_of_le_of_lt ((le_max_right _ _).trans (hM v))
      (lt_of_le_of_lt (le_max_right _ _) hs)
  · filter_upwards [hZ0, Filter.eventually_all.2 fun v => eventually_ratEval_ne_zero (hq v) (hR0 v)]
      with s h1 h2
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.2 fun v _ => h2 v)
  · filter_upwards [hZd0,
      Filter.eventually_all.2 fun v => eventually_ratEval_ne_zero (hq v) (hRd0 v)] with s h1 h2
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.2 fun v _ => h2 v)
  · intro ψv hψv νv hνv G hG
    obtain rfl : ψv = ψ0 := funext fun v => canonicalComponent_unique_tc (hψv v) (hψ0 v)
    obtain rfl : νv = ν0 := funext fun v =>
      (Correspondence.existsUnique_localSelfDualMeasure (padicField v) (ψv v)).unique
        (hνv v) (hν0 v)
    have hgam := fun v : S => (D v).exists_gammaEquation (hG v.1 v.2)
    choose ζ hζ R1 Rd1 hR1 hRd1 hfe using hgam
    have hR1e : ∀ v, R1 v = R v := fun v =>
      RankinSelberg.HasRationalContinuation.unique (hq v) (hR1 v) (hR v)
    have hRd1e : ∀ v, Rd1 v = Rd v := fun v =>
      RankinSelberg.HasRationalContinuation.unique (hq v) (hRd1 v) (hRd v)
    have hsgn := hsign ζ hζ
    have hRden : ∀ v : S, ∀ᶠ s in codiscrete ℂ,
        (R v).denom.eval (RankinSelberg.spectralPoint (q v) s) ≠ 0 := fun v =>
      eventually_polynomial_spectralPoint_ne_zero (hq v) (RatFunc.denom_ne_zero (R v))
    have hRdden : ∀ v : S, ∀ᶠ s in codiscrete ℂ,
        (Rd v).denom.eval (RankinSelberg.spectralPoint (q v) (1 - s)) ≠ 0 := fun v =>
      CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub
        (eventually_polynomial_spectralPoint_ne_zero (hq v) (RatFunc.denom_ne_zero (Rd v)))
    have hGden : ∀ v : S, ∀ᶠ s in codiscrete ℂ,
        (G v.1).denom.eval (RankinSelberg.spectralPoint (q v) s) ≠ 0 := fun v =>
      eventually_polynomial_spectralPoint_ne_zero (hq v) (RatFunc.denom_ne_zero (G v.1))
    filter_upwards [harch', Filter.eventually_all.2 hRden, Filter.eventually_all.2 hRdden,
      Filter.eventually_all.2 hGden] with s h1 h2 h3 h4
    have hloc : ∀ v : S,
        RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) (1 - s)) (Rd v) =
          (ζ v : ℂ) ^ r *
            (RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1) *
              RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v)) := by
      intro v
      have h := hfe v s (by rw [hR1e v]; exact h2 v) (by rw [hRd1e v]; exact h3 v) (h4 v)
      rw [hR1e v, hRd1e v] at h
      exact h
    have hGprod : (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) =
        ∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1) :=
      (Finset.prod_coe_sort S (fun v => RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v))).symm
    show infiniteL s * (Zd (1 - s) * ∏ v, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (q v) (1 - s)) (Rd v)) =
      (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
        infiniteEpsilon s * dualInfiniteL (1 - s) *
        (Z s * ∏ v, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v))
    rw [Finset.prod_congr rfl fun v _ => hloc v, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, hGprod]
    linear_combination
      ((∏ v : S, (ζ v : ℂ) ^ r) *
        (∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1)) *
        ∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v)) * h1 +
      ((∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1)) *
        (∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v)) *
        infiniteEpsilon s * dualInfiniteL (1 - s) * Z s) * hsgn

end Langlands.Global.RankinSelbergGlobal
