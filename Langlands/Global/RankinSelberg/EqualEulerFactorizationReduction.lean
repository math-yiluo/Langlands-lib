import Langlands.Global.RankinSelberg.EqualEulerPointwise
import Langlands.Global.RankinSelberg.EqualEulerIntegrand
import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement
import Langlands.Global.RankinSelberg.EqualEulerFactorizationStatement

/-! # Reduction of the equal-rank partial Euler factorization

`EqualEulerFactorizationStatement` follows from three statements: the one-place
factorization of spherical global Whittaker functions
(`UnramifiedWhittakerFactorizationStatement`), the one-place Iwasawa cell decomposition of
the Whittaker quotient measure (`WhittakerCellDecompositionStatement`) and the equal-rank
unfolding statement (`EqualUnfoldingStatement`), which supplies the integrability. See the
paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The equal-rank partial Euler factorization follows from the one-place factorization of
spherical global Whittaker functions, the one-place Iwasawa cell decomposition of the
Whittaker quotient measure, and the equal-rank unfolding statement. -/
def EqualEulerFactorizationReductionStatement : Prop :=
  UnramifiedWhittakerFactorizationStatement.{u, uQ} →
    WhittakerCellDecompositionStatement.{u} → EqualUnfoldingStatement.{u} →
      EqualEulerFactorizationStatement.{u, uQ}

namespace EqualEulerReduction

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa
open LocalPointFactorization EqualEulerPointwise
open CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation

local instance reductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance reductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- **The integrand on a translated class.** Let `A ⊇ S` be finite, `v ∉ A`, and let `q`
be a class whose representative lies in `N_n(F_w) GL_n(𝒪_w)` at every finite `w ∉ A`.
Then the equal-rank integrand at the class of `ι_v(ϖ_v ^ λ) q.out` is
`cellMultiplier N(v) a b s λ` times its value at `q`. -/
theorem integrand_shift (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
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
    {A : Finset (FinitePlace F)} (hSA : S ⊆ A) {v : FinitePlace F} (hvA : v ∉ A)
    {a b : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hvA (hSA (hP hvP))))
    (hb : Unramified.Eigenvalues.ofTuple b =
      P'.spectralSystem.eigenvalues v (fun hvP => hvA (hSA (hP' hvP))))
    (lam : Fin (r + 1) → ℤ) (s : ℂ) {q : WhittakerQuotient F (r + 1)}
    (hq : q ∈ unipotentIntegralClasses F (r + 1) A) :
    equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s
        (LeftCosetSpace.mk (unipotentAdelic F (r + 1))
          (localPoint F (r + 1) v (torus (placeUniformizer v) lam) * q.out)) =
      cellMultiplier (Ideal.absNorm v.asIdeal) a b s lam *
        equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
          (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s q := by
  have hv : v ∉ S := fun h => hvA (hSA h)
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v q.out) := hq v hvA
  rw [EqualEulerIntegrand.equalWhittakerIntegrand_mk T T' ψ.complex hstd x x' Φ s,
    integrand_localPoint_torus_mul hA ψ hψ hP hP' hψS hx hx' hΦ hv ha hb lam s hg,
    ← EqualEulerIntegrand.equalWhittakerIntegrand_mk T T' ψ.complex hstd x x' Φ s q.out]
  have hq' : LeftCosetSpace.mk (unipotentAdelic F (r + 1)) q.out = q := Quotient.out_eq q
  rw [hq']

/-- **The one-place step.** Let `f` be the equal-rank integrand, assumed integrable, let
`A ⊇ S` be finite and `v ∉ A`. If the Satake parameters of `P` and `P'` are bounded by
`q_v ^ C` and `q_v ^ C'` and `localRadius r C C' < Re s`, then adding `v` to `A` multiplies
the partial integral by `L(s, Π_v × Π'_v)`. -/
theorem setIntegral_insert (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (hB : WhittakerCellDecompositionStatement.{u})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {C C' : ℝ} (hC : HasSatakeBound P C) (hC' : HasSatakeBound P' C')
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x')
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ) {s : ℂ}
    (hs : EqualEulerLocal.localRadius r C C' < s.re)
    (hint : Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
      (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s) (whittakerQuotientMeasure F (r + 1)))
    {A : Finset (FinitePlace F)} (hSA : S ⊆ A) (v : {v : FinitePlace F // v ∉ S})
    (hvA : v.1 ∉ A) :
    ∫ q in unipotentIntegralClasses F (r + 1) (Finset.cons v.1 A hvA),
        equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
          (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s q ∂whittakerQuotientMeasure F (r + 1) =
      partialEulerFactor P P' hP hP' v s *
        ∫ q in unipotentIntegralClasses F (r + 1) A,
          equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
            (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s q ∂whittakerQuotientMeasure F (r + 1) := by
  classical
  set f := equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
    (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s with hfdef
  set I := ∫ q in unipotentIntegralClasses F (r + 1) A, f q ∂whittakerQuotientMeasure F (r + 1)
    with hIdef
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (P.spectralSystem.eigenvalues v.1 fun h => v.2 (hP h))
  obtain ⟨b, hb⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (P'.spectralSystem.eigenvalues v.1 fun h => v.2 (hP' h))
  have hN := CuspidalPairEulerConvergence.residueCardinality_eq_absNorm v.1
  have hcell := (hB F (r + 1) A v.1 hvA (placeUniformizer v.1)
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
      (fun q hq => integrand_shift hA ψ hψ hP hP' hψS hx hx' hΦ hSA hvA ha hb lam s hq),
      integral_const_mul, ← mul_assoc,
      zpow_modulusExponent_mul_cellMultiplier (absNorm_pos v.1)]
  have hloc := EqualEulerLocal.hasSum_equalRankLocalTerm_eulerFactor a b ha hb
    (q := Ideal.absNorm v.1.asIdeal)
    (by rw [← hN]; exact CuspidalPairEulerConvergence.two_le_residueCardinality v.1)
    (C := C) (C' := C')
    (fun α hα => by
      have h := hC v.1 (fun h => v.2 (hP h)) α hα
      rwa [hN] at h)
    (fun β hβ => by
      have h := hC' v.1 (fun h => v.2 (hP' h)) β hβ
      rwa [hN] at h) hs
  have h' : HasSum (fun lam : Fin (r + 1) → ℤ =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
          ∫ q in unipotentIntegralClasses F (r + 1) A,
            f (LeftCosetSpace.mk (unipotentAdelic F (r + 1))
              (localPoint F (r + 1) v.1 (torus (placeUniformizer v.1) lam) * q.out))
            ∂whittakerQuotientMeasure F (r + 1)) (partialEulerFactor P P' hP hP' v s * I) := by
    have h := hloc.mul_right I
    rw [partialEulerFactor, hN]
    convert h using 1
    funext lam
    exact hterm lam
  rw [Finset.cons_eq_insert]
  exact hcell.unique h'

end EqualEulerReduction

open EqualEulerReduction in
/-- **The reduction.** The one-place factorization of spherical global Whittaker functions,
the one-place Iwasawa cell decomposition of the Whittaker quotient measure and the
equal-rank unfolding statement imply the equal-rank partial Euler factorization. -/
theorem equalEulerFactorizationReduction :
    EqualEulerFactorizationReductionStatement.{u, uQ} := by
  intro hA hB hU F _ _ _ ψ hψ r T T' P P' S hP hP' hψS
  obtain ⟨C0, hC0⟩ :=
    EqualEulerIntegrand.exists_integrable_equalWhittakerIntegrand_unitary hU F ψ hψ r T T'
  obtain ⟨σ2, hσ2⟩ := exists_partialEulerFactor_convergence P P' hP hP'
  obtain ⟨C, hC⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨C', hC'⟩ := exists_hasSatakeBound_presentation T' P'
  refine ⟨max C0 (max σ2 (EqualEulerLocal.localRadius r C C')), ?_⟩
  intro x x' Φ hx hx' hΦs hΦ W W' s hs
  have hs0 : C0 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : σ2 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsl : EqualEulerLocal.localRadius r C C' < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hint := hC0 x x' Φ hΦs s hs0
  obtain ⟨hsum, hprod⟩ := hσ2 s hs2
  refine ⟨hint, hsum, partialEulerProduct P P' hP hP' s, hprod, ?_⟩
  rw [partialEqualWhittakerIntegral_eq_setIntegral]
  exact (integral_eq_hasProd_mul_setIntegral hint hprod
    (fun A hSA v hvA => setIntegral_insert hA hB ψ hψ hP hP' hψS hC hC' hx hx' hΦ hsl hint
      hSA v hvA)).trans (mul_comm _ _)

end Langlands.Global.RankinSelbergGlobal
