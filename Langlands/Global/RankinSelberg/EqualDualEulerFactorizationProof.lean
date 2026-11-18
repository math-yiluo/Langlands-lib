import Langlands.Global.RankinSelberg.ContragredientDualSplit
import Langlands.Global.RankinSelberg.EqualEulerFactorizationReduction
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition
import Langlands.Global.RankinSelberg.EqualGaugeDualSpecialization
import Langlands.Global.RankinSelberg.EqualUnfoldingReduction
import Langlands.Global.RankinSelberg.WhittakerSchwartzGauge
import Langlands.Global.RankinSelberg.FourierStandardOutsideProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationStatement

/-! # Proof of the partial Euler factorization of the equal-rank dual Whittaker integral

`EqualDualEulerFactorizationStatement` is proved directly, one place at a time, as in
`equalEulerFactorization_of_gauge`. The splitting of the dual Whittaker functions at unramified
places is `ContragredientDualSplit.dualWhittaker_split`, the integrability is the dual gauge
estimate `integrable_dualEqualWhittakerIntegrand_of_gauge` with `whittakerSchwartzGauge`, and
the Fourier transform of a test function standard outside `S` is standard outside `S` by
`fourierStandardOutside`. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace EqualDualEuler

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open LocalPointFactorization EqualEulerPointwise
open Langlands.Global.CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation
open UnequalDualEuler ContragredientDualSplit

local instance equalDualProofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalDualProofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The equal-rank integrand of `W̃ = dual of W_x^ψ` and `W̃' = dual of W_(x')^(ψ⁻¹)` at the
class of any `g` is `W̃(g) W̃'(g) Φ(e_n g) |det g|^s`: the two generic characters cancel. -/
theorem dualIntegrand_mk {r : ℕ} (T T' : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (x : T.Space)
    (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (g : Points F (r + 1)) :
    equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ x))
        (dualFunction F (r + 1) (cuspWhittaker F T' ψ⁻¹ x')) Φ s
        (LeftCosetSpace.mk (unipotentAdelic F (r + 1)) g) =
      dualFunction F (r + 1) (cuspWhittaker F T ψ x) g *
        dualFunction F (r + 1) (cuspWhittaker F T' ψ⁻¹ x') g * Φ (lastRow F r g) *
        detPower F (r + 1) g s := by
  obtain ⟨u, hu⟩ := Unfolding.exists_out_mk_eq (unipotentAdelic F (r + 1)) g
  have hψi := Unfolding.isStandardAdditiveCharacter_inv F ψ hψ
  have hχ := Unfolding.genericCharacter_ne_zero F r ψ hψ (fun _ => 1) u
  have h1 := Unfolding.dualCuspWhittaker_unipotent_mul F T ψ⁻¹ hψi x u g
  rw [inv_inv] at h1
  have h2 := Unfolding.dualCuspWhittaker_unipotent_mul F T' ψ hψ x' u g
  simp only [equalWhittakerIntegrand]
  rw [hu, h1, h2, EqualEulerIntegrand.lastRow_unipotent_mul, Unfolding.detPower_unipotent_mul,
    Unfolding.genericCharacter_inv_eq_inv, mul_mul_mul_comm, inv_mul_cancel₀ hχ, one_mul]

/-- **The dual Whittaker part.** At `v ∉ S` where `ψ_v` has conductor `𝒪_v`, and `g` with
`g_v ∈ N_n(F_v) GL_n(𝒪_v)`,
`W̃(ι_v(ϖ_v ^ λ) g) W̃'(ι_v(ϖ_v ^ λ) g) = W°_a(ϖ_v ^ λ) W°_b(ϖ_v ^ λ) W̃(g) W̃'(g)`, where
`a`, `b` are Satake parameters of the presentations `Pd`, `Pd'` of the contragredients. -/
theorem dualWhittaker_mul_localPoint_torus
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T Td T' Td' : Automorphic.CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a b : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (lam : Fin (r + 1) → ℤ) {g : Points F (r + 1)}
    (hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v g)) :
    dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) *
        dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) =
      (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur a lam
          else 0) *
        (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur b lam
          else 0) *
        (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g *
          dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g) := by
  have hϖ := isUniformizingElement_canonical v
  have hq := EqualEulerPointwise.residueCardinality_canonical v
  set t := torus (placeUniformizer v) lam with ht
  set gv := finiteComponent F (r + 1) v g with hgv
  set g' := g * (localPoint F (r + 1) v gv)⁻¹ with hg'def
  have hg' : finiteComponent F (r + 1) v g' = 1 :=
    finiteComponent_mul_inv_localPoint F (r + 1) v g
  have hgg : g = g' * localPoint F (r + 1) v gv := by rw [hg'def, inv_mul_cancel_right]
  have hmul : localPoint F (r + 1) v t * g = g' * localPoint F (r + 1) v (t * gv) :=
    localPoint_mul_eq F (r + 1) v t g
  have hs1 := (dualWhittaker_split F ψ hψ hTd Pd hPd hx hv hψv h0 ha).1 g' hg'
  have hs2 := (dualWhittaker_split F ψ hψ hTd' Pd' hPd' hx' hv hψv h0 hb).2 g' hg'
  have hθ : ∀ u, (@Whittaker.inverseStandardCharacter _ _
      (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r) u *
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r) u = 1 :=
    fun u => inv_mul_cancel _
  obtain ⟨u, hu, k, hk, hgvuk⟩ := exists_eq_mul_of_isUnipotentIntegral v hg
  have hexp : exponent hϖ (t * gv) = lam := by
    rw [hgvuk]; exact exponent_torus_mul hϖ lam hu hk
  have hexp0 : exponent hϖ gv = 0 := by
    rw [hgvuk]; exact exponent_unipotent_mul_integral hϖ hu hk
  have e1 : sphInv v ψv r a (t * gv) * sphStd v ψv r b (t * gv) =
      (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur a lam
          else 0) *
        (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur b lam
          else 0) := by
    unfold sphInv sphStd
    rw [hq]
    exact sphericalWhittaker_mul_sphericalWhittaker hϖ hθ (Ideal.absNorm v.asIdeal) a b hexp
  have e0 : sphInv v ψv r a gv * sphStd v ψv r b gv = 1 := by
    unfold sphInv sphStd
    rw [hq]
    exact sphericalWhittaker_mul_sphericalWhittaker_of_exponent_eq_zero hϖ hθ
      (Ideal.absNorm v.asIdeal) a b hexp0
  have f1 : dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g =
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g' * sphInv v ψv r a gv := by
    conv_lhs => rw [hgg]
    exact hs1 gv
  have f2 : dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g =
      dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g' * sphStd v ψv r b gv := by
    conv_lhs => rw [hgg]
    exact hs2 gv
  rw [hmul, hs1 (t * gv), hs2 (t * gv), f1, f2]
  linear_combination
    (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g' *
        dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g') * e1 -
      ((if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur a lam
          else 0) *
        (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur b lam
          else 0)) *
        (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g' *
          dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g') * e0

/-- **The pointwise identity.** At `v ∉ S` where `ψ_v` has conductor `𝒪_v`, `g` with
`g_v ∈ N_n(F_v) GL_n(𝒪_v)` and `Φ` standard outside `S`, the dual equal-rank integrand at
`ι_v(ϖ_v ^ λ) g` is `cellMultiplier N(v) a b s λ` times its value at `g`. -/
theorem dualIntegrand_localPoint_torus_mul
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T Td T' Td' : Automorphic.CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ)
    {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a b : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (lam : Fin (r + 1) → ℤ) (s : ℂ) {g : Points F (r + 1)}
    (hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v g)) :
    dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) *
        dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) *
        Φ (lastRow F r (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g)) *
        detPower F (r + 1) (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) s =
      cellMultiplier (Ideal.absNorm v.asIdeal) a b s lam *
        (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g *
          dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g *
          Φ (lastRow F r g) * detPower F (r + 1) g s) := by
  have hN := absNorm_pos v
  rw [dualWhittaker_mul_localPoint_torus ψ hψ hTd hTd' Pd Pd' hPd hPd' hx hx' hv hψv h0 ha hb
      lam hg,
    EqualEulerSchwartz.apply_lastRow_localPoint_torus hΦ hv (placeUniformizer v)
      (isUniformizingElement_valued v) lam g hg,
    detPower_localPoint_mul F (r + 1) v _ g s, log_norm_det_torus, cellMultiplier]
  by_cases hanti : Antitone lam
  · by_cases hlast : 0 ≤ lam (Fin.last r)
    · have hsum : 0 ≤ ∑ i, lam i :=
        Finset.sum_nonneg fun i _ => le_trans hlast (hanti (Fin.le_last i))
      have hlog : Real.log ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(((∑ i, lam i).toNat : ℕ) : ℤ))) =
          -((∑ i, lam i : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
        rw [Real.log_zpow, Int.toNat_of_nonneg hsum]
        push_cast
        ring
      rw [← hlog, EqualEulerLocal.exp_mul_log_zpow_eq_spectralPoint_pow hN]
      simp only [hlast, ↓reduceIte]
      ring
    · simp only [hlast, ↓reduceIte]
      ring
  · simp only [hanti, ↓reduceIte]
    ring

/-- **The integrand on a translated class.** Let `A ⊇ S` be finite, `v ∉ A`, and `q` a class
whose representative lies in `N_n(F_w) GL_n(𝒪_w)` at every finite `w ∉ A`. Then the dual
equal-rank integrand at the class of `ι_v(ϖ_v ^ λ) q.out` is `cellMultiplier N(v) a b s λ`
times its value at `q`. -/
theorem integrand_shift
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T Td T' Td' : Automorphic.CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ)
    {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a b : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (lam : Fin (r + 1) → ℤ) (s : ℂ) {A : Finset (FinitePlace F)} (hvA : v ∉ A)
    {q : WhittakerQuotient F (r + 1)} (hq : q ∈ unipotentIntegralClasses F (r + 1) A) :
    equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
        (dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) Φ s
        (LeftCosetSpace.mk (unipotentAdelic F (r + 1))
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * q.out)) =
      cellMultiplier (Ideal.absNorm v.asIdeal) a b s lam *
        equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
          (dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) Φ s q := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v q.out) := hq v hvA
  rw [dualIntegrand_mk T T' ψ.complex hstd x x' Φ s,
    dualIntegrand_localPoint_torus_mul ψ hψ hTd hTd' Pd Pd' hPd hPd' hx hx' hΦ hv hψv h0 ha hb
      lam s hg,
    ← dualIntegrand_mk T T' ψ.complex hstd x x' Φ s q.out]
  have hq' : LeftCosetSpace.mk (unipotentAdelic F (r + 1)) q.out = q := Quotient.out_eq q
  rw [hq']

/-- **The one-place step.** Let `f` be the dual equal-rank integrand, assumed integrable, let
`A ⊇ S` be finite and `v ∉ A`. If the Satake parameters of `Pd` and `Pd'` are bounded by
`q_v ^ C` and `q_v ^ C'` and `localRadius r C C' < Re s`, then adding `v` to `A` multiplies
the partial integral by `L(s, Π̃_v × Π̃'_v)`. -/
theorem setIntegral_insert
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T Td T' Td' : Automorphic.CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {C C' : ℝ} (hC : HasSatakeBound Pd C) (hC' : HasSatakeBound Pd' C')
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ) {s : ℂ}
    (hs : EqualEulerLocal.localRadius r C C' < s.re)
    (hint : Integrable (equalWhittakerIntegrand F
      (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
      (dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) Φ s)
      (whittakerQuotientMeasure F (r + 1)))
    {A : Finset (FinitePlace F)} (v : {v : FinitePlace F // v ∉ S}) (hvA : v.1 ∉ A) :
    ∫ q in unipotentIntegralClasses F (r + 1) (Finset.cons v.1 A hvA),
        equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
          (dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) Φ s q
        ∂whittakerQuotientMeasure F (r + 1) =
      partialEulerFactor Pd Pd' hPd hPd' v s *
        ∫ q in unipotentIntegralClasses F (r + 1) A,
          equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
            (dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) Φ s q
          ∂whittakerQuotientMeasure F (r + 1) := by
  classical
  set f := equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
    (dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) Φ s with hfdef
  set I := ∫ q in unipotentIntegralClasses F (r + 1) A, f q ∂whittakerQuotientMeasure F (r + 1)
    with hIdef
  obtain ⟨ψv, hψv, h0⟩ := hψS v.1 v.2
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (Pd.spectralSystem.eigenvalues v.1 fun h => v.2 (hPd h))
  obtain ⟨b, hb⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (Pd'.spectralSystem.eigenvalues v.1 fun h => v.2 (hPd' h))
  have hN := CuspidalPairEulerConvergence.residueCardinality_eq_absNorm v.1
  have hcell := (whittakerCellDecomposition F (r + 1) A v.1 hvA (placeUniformizer v.1)
    (isUniformizingElement_valued v.1) f hint).2
  have hterm : ∀ lam : Fin (r + 1) → ℤ,
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
          ∫ q in unipotentIntegralClasses F (r + 1) A,
            f (LeftCosetSpace.mk (unipotentAdelic F (r + 1))
              (localPoint F (r + 1) v.1 (torus (placeUniformizer v.1) lam) * q.out))
            ∂whittakerQuotientMeasure F (r + 1) =
        EqualEulerLocal.equalRankLocalTerm a b
          (RankinSelberg.spectralPoint (Ideal.absNorm v.1.asIdeal) s) lam * I := by
    intro lam
    rw [setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (r + 1) A)
      (fun q hq => integrand_shift ψ hψ hTd hTd' Pd Pd' hPd hPd' hx hx' hΦ v.2 hψv h0 ha hb
        lam s hvA hq),
      integral_const_mul, ← mul_assoc,
      zpow_modulusExponent_mul_cellMultiplier (absNorm_pos v.1)]
  have hloc := EqualEulerLocal.hasSum_equalRankLocalTerm_eulerFactor a b ha hb
    (q := Ideal.absNorm v.1.asIdeal)
    (by rw [← hN]; exact CuspidalPairEulerConvergence.two_le_residueCardinality v.1)
    (C := C) (C' := C')
    (fun α hα => by
      have h := hC v.1 (fun h => v.2 (hPd h)) α hα
      rwa [hN] at h)
    (fun β hβ => by
      have h := hC' v.1 (fun h => v.2 (hPd' h)) β hβ
      rwa [hN] at h) hs
  have h' : HasSum (fun lam : Fin (r + 1) → ℤ =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
          ∫ q in unipotentIntegralClasses F (r + 1) A,
            f (LeftCosetSpace.mk (unipotentAdelic F (r + 1))
              (localPoint F (r + 1) v.1 (torus (placeUniformizer v.1) lam) * q.out))
            ∂whittakerQuotientMeasure F (r + 1)) (partialEulerFactor Pd Pd' hPd hPd' v s * I) := by
    have h := hloc.mul_right I
    rw [partialEulerFactor, hN]
    convert h using 1
    funext lam
    exact hterm lam
  rw [Finset.cons_eq_insert]
  exact hcell.unique h'

end EqualDualEuler

open EqualDualEuler in
/-- **Cogdell 2004, pp.210–211 and 219–220, with Theorem 3.3, p.215**: the partial Euler
factorization of the equal-rank dual global Whittaker integral. -/
theorem equalDualEulerFactorization : EqualDualEulerFactorizationStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hψS
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨C0, -, hC0⟩ := integrable_dualEqualWhittakerIntegrand_of_gauge F
    (equalGaugeDualSpecialization whittakerSchwartzGauge F r T T')
  obtain ⟨σ2, hσ2⟩ := exists_partialEulerFactor_convergence Pd Pd' hPd hPd'
  obtain ⟨C, hC⟩ := exists_hasSatakeBound_presentation Td Pd
  obtain ⟨C', hC'⟩ := exists_hasSatakeBound_presentation Td' Pd'
  refine ⟨max C0 (max σ2 (EqualEulerLocal.localRadius r C C')), ?_⟩
  intro x x' Φ hx hx' hΦs hΦ Wdual W'dual Φhat s hs
  have hs0 : C0 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : σ2 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsl : EqualEulerLocal.localRadius r C C' < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hΦhat : IsStandardOutside F (r + 1) S Φhat :=
    fourierStandardOutside F ψ S hψS (r + 1) Φ hΦ
  have hint := hC0 ψ.complex hstd x x' Φ hΦs s hs0
  obtain ⟨hsum, hprod⟩ := hσ2 s hs2
  refine ⟨hint, hsum, partialEulerProduct Pd Pd' hPd hPd' s, hprod, ?_⟩
  rw [partialEqualWhittakerIntegral_eq_setIntegral]
  exact (integral_eq_hasProd_mul_setIntegral hint hprod
    (fun A _ v hvA => setIntegral_insert ψ hψ hTd hTd' Pd Pd' hPd hPd' hψS hC hC' hx hx'
      hΦhat hsl hint v hvA)).trans (mul_comm _ _)

end Langlands.Global.RankinSelbergGlobal
