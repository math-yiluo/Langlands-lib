import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationStatement
import Langlands.Global.RankinSelberg.EqualEulerLocalSum
import Langlands.Global.RankinSelberg.EqualEulerSchwartzPart
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge

/-! # The equal-rank Whittaker integrand on one Iwasawa cell

At a finite place `v ∉ S`, left translation by the point `ι_v(ϖ_v ^ λ)` multiplies the
equal-rank Whittaker integrand `W(g) W'(g) Φ(e_n g) |det g|^s`, at every `g` with
`g_v ∈ N_n(F_v) GL_n(𝒪_v)`, by the number `cellMultiplier`. Weighted by the inverse modulus
`δ_B⁻¹(ϖ_v ^ λ)`, that number is the torus term whose sum over `λ` is the unramified pair
Euler factor. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open LocalPointFactorization

local instance pointwiseSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance pointwiseSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### The cell multiplier -/

/-- The multiplier of the equal-rank integrand on the cell of `λ`:
`W°_a(ϖ ^ λ) W°_b(ϖ ^ λ) 1[λ_n ≥ 0] t ^ (λ_1 + ⋯ + λ_n)` with `t = q ^ (-s)`, where
`W°_a(ϖ ^ λ) = δ_B ^ (1/2)(ϖ ^ λ) s_λ(a)` for antitone `λ` and `0` otherwise. -/
def cellMultiplier (q : ℕ) {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (s : ℂ)
    (lam : Fin (n + 1) → ℤ) : ℂ :=
  (if Antitone lam then halfModulus q lam * satakeSchur a lam else 0) *
    (if Antitone lam then halfModulus q lam * satakeSchur b lam else 0) *
    (if 0 ≤ lam (Fin.last n) then RankinSelberg.spectralPoint q s ^ (∑ i, lam i).toNat else 0)

/-- `∑_(i<j) (λ_i - λ_j) = ∑_i (n - 2 i) λ_i`. -/
theorem modulusExponent_eq {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    modulusExponent lam = ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i := by
  rw [modulusExponent, ← EqualEulerLocal.sum_sub_of_lt_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- The inverse modulus times the cell multiplier is the equal-rank torus term. -/
theorem zpow_modulusExponent_mul_cellMultiplier {q : ℕ} (hq : 0 < q) {n : ℕ}
    (a b : Fin (n + 1) → ℂˣ) (s : ℂ) (lam : Fin (n + 1) → ℤ) :
    (q : ℂ) ^ modulusExponent lam * cellMultiplier q a b s lam =
      EqualEulerLocal.equalRankLocalTerm a b (RankinSelberg.spectralPoint q s) lam := by
  rw [modulusExponent_eq, cellMultiplier]
  exact EqualEulerLocal.torusTerm_eq_equalRankLocalTerm hq a b _ lam

/-! ### The Whittaker part -/

/-- The residue cardinality of the canonical realization of `F_v` is `N(v)`. -/
theorem residueCardinality_canonical {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) :
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality =
      Ideal.absNorm v.asIdeal := by
  rw [← CompletionPadic.topologicalData_eq_canonicalTopologicalData]
  exact HeckeEulerProduct.residueCardinality_eq v

theorem absNorm_pos {F : Type u} [Field F] [NumberField F] (v : FinitePlace F) :
    0 < Ideal.absNorm v.asIdeal := by
  have h := NumberField.HeightOneSpectrum.one_lt_absNorm v
  omega

section Whittaker

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- **The Whittaker part.** At `v ∉ S` and `g` with `g_v ∈ N_n(F_v) GL_n(𝒪_v)`,
`W(ι_v(ϖ_v ^ λ) g) W'(ι_v(ϖ_v ^ λ) g) = W°_a(ϖ_v ^ λ) W°_b(ϖ_v ^ λ) W(g) W'(g)`, from the
one-place factorization `UnramifiedWhittakerFactorizationStatement`. -/
theorem whittaker_mul_localPoint_torus (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x')
    {v : FinitePlace F} (hv : v ∉ S) {a b : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (hb : Unramified.Eigenvalues.ofTuple b =
      P'.spectralSystem.eigenvalues v (fun hvP => hv (hP' hvP)))
    (lam : Fin (r + 1) → ℤ) {g : Points F (r + 1)}
    (hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v g)) :
    cuspWhittaker F T ψ.complex x
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) *
        cuspWhittaker F T' ψ.complex⁻¹ x'
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) =
      (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur a lam
          else 0) *
        (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur b lam
          else 0) *
        (cuspWhittaker F T ψ.complex x g * cuspWhittaker F T' ψ.complex⁻¹ x' g) := by
  obtain ⟨ψv, hψv, -⟩ := hψS v hv
  have hϖ := isUniformizingElement_canonical v
  have hq := residueCardinality_canonical v
  set t := torus (placeUniformizer v) lam with ht
  set gv := finiteComponent F (r + 1) v g with hgv
  set g' := g * (localPoint F (r + 1) v gv)⁻¹ with hg'def
  have hg' : finiteComponent F (r + 1) v g' = 1 :=
    finiteComponent_mul_inv_localPoint F (r + 1) v g
  have hgg : g = g' * localPoint F (r + 1) v gv := by rw [hg'def, inv_mul_cancel_right]
  have hmul : localPoint F (r + 1) v t * g = g' * localPoint F (r + 1) v (t * gv) :=
    localPoint_mul_eq F (r + 1) v t g
  set θ := @Whittaker.standardCharacter _ _
    (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r with hθdef
  set θ' := @Whittaker.inverseStandardCharacter _ _
    (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r with hθ'def
  have hθ : ∀ u, θ u * θ' u = 1 := fun u => mul_inv_cancel (θ u)
  have h1 := hA F ψ hψ r T P S hP hψS x hx v hv ψv hψv (placeUniformizer v) hϖ a ha g' hg'
    (t * gv)
  have h2 := hA F ψ hψ r T P S hP hψS x hx v hv ψv hψv (placeUniformizer v) hϖ a ha g' hg' gv
  have h1' := hA F ψ hψ r T' P' S hP' hψS x' hx' v hv ψv hψv (placeUniformizer v) hϖ b hb g'
    hg' (t * gv)
  have h2' := hA F ψ hψ r T' P' S hP' hψS x' hx' v hv ψv hψv (placeUniformizer v) hϖ b hb g'
    hg' gv
  have e1 : cuspWhittaker F T ψ.complex x (g' * localPoint F (r + 1) v (t * gv)) =
      cuspWhittaker F T ψ.complex x g' *
        sphericalWhittaker hϖ θ (Ideal.absNorm v.asIdeal) a (t * gv) := by
    rw [← hq]; exact h1.1
  have e2 : cuspWhittaker F T ψ.complex x g =
      cuspWhittaker F T ψ.complex x g' *
        sphericalWhittaker hϖ θ (Ideal.absNorm v.asIdeal) a gv := by
    rw [← hq]; conv_lhs => rw [hgg]
    exact h2.1
  have e1' : cuspWhittaker F T' ψ.complex⁻¹ x' (g' * localPoint F (r + 1) v (t * gv)) =
      cuspWhittaker F T' ψ.complex⁻¹ x' g' *
        sphericalWhittaker hϖ θ' (Ideal.absNorm v.asIdeal) b (t * gv) := by
    rw [← hq]; exact h1'.2
  have e2' : cuspWhittaker F T' ψ.complex⁻¹ x' g =
      cuspWhittaker F T' ψ.complex⁻¹ x' g' *
        sphericalWhittaker hϖ θ' (Ideal.absNorm v.asIdeal) b gv := by
    rw [← hq]; conv_lhs => rw [hgg]
    exact h2'.2
  obtain ⟨u, hu, k, hk, hgvuk⟩ := exists_eq_mul_of_isUnipotentIntegral v hg
  have hexp : exponent hϖ (t * gv) = lam := by
    rw [hgvuk]; exact exponent_torus_mul hϖ lam hu hk
  have hexp0 : exponent hϖ gv = 0 := by
    rw [hgvuk]; exact exponent_unipotent_mul_integral hϖ hu hk
  have hW1 := sphericalWhittaker_mul_sphericalWhittaker hϖ hθ (Ideal.absNorm v.asIdeal) a b hexp
  have hW0 := sphericalWhittaker_mul_sphericalWhittaker_of_exponent_eq_zero hϖ hθ
    (Ideal.absNorm v.asIdeal) a b hexp0
  rw [hmul, e1, e1', e2, e2']
  linear_combination
    (cuspWhittaker F T ψ.complex x g' * cuspWhittaker F T' ψ.complex⁻¹ x' g') * hW1 -
      ((if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur a lam
          else 0) *
        (if Antitone lam then halfModulus (Ideal.absNorm v.asIdeal) lam * satakeSchur b lam
          else 0)) *
        (cuspWhittaker F T ψ.complex x g' * cuspWhittaker F T' ψ.complex⁻¹ x' g') * hW0

/-- **The pointwise identity.** At `v ∉ S` and `g` with `g_v ∈ N_n(F_v) GL_n(𝒪_v)`, the
equal-rank integrand at `ι_v(ϖ_v ^ λ) g` is `cellMultiplier N(v) a b s λ` times its value
at `g`. -/
theorem integrand_localPoint_torus_mul
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ)
    {v : FinitePlace F} (hv : v ∉ S) {a b : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (hb : Unramified.Eigenvalues.ofTuple b =
      P'.spectralSystem.eigenvalues v (fun hvP => hv (hP' hvP)))
    (lam : Fin (r + 1) → ℤ) (s : ℂ) {g : Points F (r + 1)}
    (hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v g)) :
    cuspWhittaker F T ψ.complex x
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) *
        cuspWhittaker F T' ψ.complex⁻¹ x'
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) *
        Φ (lastRow F r (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g)) *
        detPower F (r + 1) (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * g) s =
      cellMultiplier (Ideal.absNorm v.asIdeal) a b s lam *
        (cuspWhittaker F T ψ.complex x g * cuspWhittaker F T' ψ.complex⁻¹ x' g *
          Φ (lastRow F r g) * detPower F (r + 1) g s) := by
  have hN := absNorm_pos v
  rw [whittaker_mul_localPoint_torus hA ψ hψ hP hP' hψS hx hx' hv ha hb lam hg,
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

end Whittaker

end Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise
