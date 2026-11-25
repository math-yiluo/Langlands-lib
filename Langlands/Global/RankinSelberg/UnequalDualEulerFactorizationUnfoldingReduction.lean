import Langlands.Global.RankinSelberg.ContragredientDualSplit
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition

/-! # The unequal-rank dual Euler factorization from the unfolding statement

`UnequalDualEulerFactorizationStatement` follows from `UnequalUnfoldingStatement` alone. The
proof follows `UnequalDualEulerFactorizationReduction`, with the splitting of the dual Whittaker
functions at unramified places taken from `ContragredientDualSplit.dualWhittaker_split` instead
of from `ContragredientDualWhittakerStatement`. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnequalDualEulerContragredient

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.RectangularSupport
open LocalPointFactorization
open Langlands.Global.CuspidalPairBoundaryNonvanishing
open UnequalDualEuler ContragredientDualSplit

local instance unequalDualContragredientSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalDualContragredientSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### The dual kernel on the cells at `v` -/

section Kernel

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- `W̃(rect(ι_v(Q) g, y) w) = W°⁻(diag(Q, I)) W̃(rect(g, y) w)` for the dual `W̃` of the
`ψ`-Whittaker function of `x`, when `g_v ∈ GL_(t+1)(𝒪_v)`. -/
theorem dualFunction_rectangularPoint_localPoint_mul
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (Q : FiniteLocalGL F (t + 1) v) {g : Points F (t + 1)}
    (hg : finiteComponent F (t + 1) v g ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t)
    (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)
        (rectangularPoint F h (localPoint F (t + 1) v Q * g) y * unfoldingWeyl F h) =
      sphInv v ψv r a (rectGL h Q 0) *
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)
          (rectangularPoint F h g y * unfoldingWeyl F h) := by
  rw [Unfolding.rectangularPoint_mul_left, pad_localPoint F h, mul_assoc]
  refine apply_localPoint_mul_of_split v
    (dualWhittaker_split F ψ hψ hTd Pd hPd hx hv hψv h0 ha).1 _ _ ?_
  rw [finiteComponent_mul, finiteComponent_rectangularPoint F h]
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  unfold sphInv
  exact sphericalWhittaker_inverseStandard_rectGL_zero_mul h (isUniformizingElement_canonical v)
    (integer_trivial_of_conductor h0) (exists_ne_one_of_conductor h0) _ a Q hg _
    (finiteComponent_unfoldingWeyl_mem h v)

/-- `W̃'(ι_v(Q) g) = W°(Q) W̃'(g)` for the dual `W̃'` of the `ψ⁻¹`-Whittaker function of `x'`,
when `g_v ∈ GL_(t+1)(𝒪_v)`. -/
theorem dualFunction_localPoint_mul_of_integral
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {t : ℕ}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd' : Pd'.exceptional ⊆ S)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (Q : FiniteLocalGL F (t + 1) v) {g : Points F (t + 1)}
    (hg : finiteComponent F (t + 1) v g ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t) :
    dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') (localPoint F (t + 1) v Q * g) =
      sphStd v ψv t b Q * dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x') g := by
  refine apply_localPoint_mul_of_split v
    (dualWhittaker_split F ψ hψ hTd' Pd' hPd' hx' hv hψv h0 hb).2 Q g ?_
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_standardCharacter (integer_trivial_of_conductor h0) t
  unfold sphStd
  rw [sphericalWhittaker_mul_integral _ _ _ hθ Q hg]
  have h1 : sphericalWhittaker (isUniformizingElement_canonical v)
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv t)
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality b
      (finiteComponent F (t + 1) v g) = 1 := by
    rw [← one_mul (finiteComponent F (t + 1) v g), sphericalWhittaker_mul_integral _ _ _ hθ 1 hg,
      sphericalWhittaker_one _ _ _ hθ]
  rw [h1, mul_one]

/-- The dual kernel of `(W̃, W̃')` at `ι_v(Q) g` is `cellFactor Q` times its value at `g`, when
`g_v ∈ GL_(t+1)(𝒪_v)`. -/
theorem dualKernel_localPoint_mul_of_integral
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) (Q : FiniteLocalGL F (t + 1) v) {g : Points F (t + 1)}
    (hg : finiteComponent F (t + 1) v g ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t) :
    Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s
        (localPoint F (t + 1) v Q * g) =
      cellFactor h v ψv a b s Q *
        Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s g := by
  have hrect : Unfolding.dualRectIntegral F h (Unfolding.dualWhittaker F h T ψ.complex x)
      (localPoint F (t + 1) v Q * g) =
      sphInv v ψv r a (rectGL h Q 0) *
        Unfolding.dualRectIntegral F h (Unfolding.dualWhittaker F h T ψ.complex x) g := by
    unfold Unfolding.dualRectIntegral Unfolding.dualWhittaker translateFunction
    simp_rw [dualFunction_rectangularPoint_localPoint_mul ψ hψ h hTd Pd hPd hx hv hψv h0 ha Q hg]
    exact integral_const_mul _ _
  unfold Unfolding.dualKernel
  rw [hrect, dualFunction_localPoint_mul_of_integral ψ hψ hTd' Pd' hPd' hx' hv hψv h0 hb Q hg,
    detPower_localPoint_mul, cellFactor]
  ring

/-- **The cell property of the dual kernel.** At `g` with `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`,
the dual kernel at `ι_v(ϖ_v^λ) g` is `cellFactor (ϖ_v^λ)` times its value at `g`. -/
theorem dualKernel_localPoint_torus_mul
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) (lam : Fin (t + 1) → ℤ) {g : Points F (t + 1)}
    (hg : IsUnipotentIntegral F (t + 1) v (finiteComponent F (t + 1) v g)) :
    Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s
        (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * g) =
      cellFactor h v ψv a b s (torus (placeUniformizer v) lam) *
        Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s g := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hN : ∀ n ∈ unipotentAdelic F (t + 1), ∀ y,
      Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s (n * y) =
        Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s y :=
    fun n hn y => Unfolding.dualKernel_whittaker_unipotent_mul F h T T' ψ.complex hstd x x' s
      ⟨n, hn⟩ y
  obtain ⟨u, hu, k, hk, hgv⟩ := exists_eq_mul_of_isUnipotentIntegral v hg
  obtain ⟨g₁, rfl⟩ : ∃ g₁, g = localPoint F (t + 1) v u * g₁ :=
    ⟨(localPoint F (t + 1) v u)⁻¹ * g, by group⟩
  have hg₁ : finiteComponent F (t + 1) v g₁ = k := by
    rw [finiteComponent_mul, finiteComponent_localPoint] at hgv
    exact mul_left_cancel hgv
  set ϖt := torus (placeUniformizer v) lam with hϖt
  have e : localPoint F (t + 1) v ϖt * (localPoint F (t + 1) v u * g₁) =
      localPoint F (t + 1) v (ϖt * u * ϖt⁻¹) * (localPoint F (t + 1) v ϖt * g₁) := by
    rw [← mul_assoc (localPoint F (t + 1) v (ϖt * u * ϖt⁻¹)), ← localPoint_mul,
      inv_mul_cancel_right, localPoint_mul, mul_assoc]
  rw [e, hN _ (localPoint_mem_unipotentAdelic F v (torus_mul_mul_inv_mem _ lam hu)),
    hN _ (localPoint_mem_unipotentAdelic F v hu)]
  exact dualKernel_localPoint_mul_of_integral ψ hψ h hTd hTd' Pd Pd' hPd hPd' hx hx' hv hψv h0
    ha hb s _ (by rw [hg₁]; exact hk)

end Kernel

/-! ### The one-place step -/

section Step

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The dual integrand at the class of `ι_v(ϖ_v^λ) g` is `cellFactor (ϖ_v^λ)` times its value at
the class of `g`, for classes with `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`. -/
theorem integrand_shift
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) (lam : Fin (t + 1) → ℤ) {A : Finset (FinitePlace F)} (hvA : v ∉ A)
    {q : WhittakerQuotient F (t + 1)} (hq : q ∈ unipotentIntegralClasses F (t + 1) A) :
    dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s
        (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
          (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out)) =
      cellFactor h v ψv a b s (torus (placeUniformizer v) lam) *
        dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  rw [Unfolding.dualWhittakerIntegrand_eq, Unfolding.dualWhittakerIntegrand_eq]
  obtain ⟨n, hn⟩ := Unfolding.exists_out_mk_eq (unipotentAdelic F (t + 1))
    (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out)
  rw [hn, Unfolding.dualKernel_whittaker_unipotent_mul F h T T' ψ.complex hstd x x' s n]
  exact dualKernel_localPoint_torus_mul ψ hψ h hTd hTd' Pd Pd' hPd hPd' hx hx' hv hψv h0 ha hb
    s lam ((show q.out ∈ unipotentIntegralOutside F (t + 1) A from hq) v hvA)

/-- **The one-place step.** Adding a finite place `v ∉ A` to the set `A` multiplies the partial
dual integral over `unipotentIntegralClasses F (t+1) A` by the sum `L` of the local terms at
`v`. -/
theorem setIntegral_cons_eq
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hTd' : Td'.realization.IsContragredientOf T'.realization)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x)
    {x' : T'.Space} (hx' : IsSphericalOutside F T' S x') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) {L : ℂ}
    (hL : HasSum (_root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.localTerm
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a b s) L)
    (hf : Integrable (dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
      (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s)
      (whittakerQuotientMeasure F (t + 1)))
    {A : Finset (FinitePlace F)} (hvA : v ∉ A) :
    ∫ q in unipotentIntegralClasses F (t + 1) (Finset.cons v A hvA),
        dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q
        ∂whittakerQuotientMeasure F (t + 1) =
      L * ∫ q in unipotentIntegralClasses F (t + 1) A,
        dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q
        ∂whittakerQuotientMeasure F (t + 1) := by
  classical
  set f := dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
    (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s with hfdef
  obtain ⟨-, hsum⟩ := whittakerCellDecomposition F (t + 1) A v hvA (placeUniformizer v)
    (isUniformizingElement_valued v) f hf
  have hterm : ∀ lam : Fin (t + 1) → ℤ,
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
          ∫ q in unipotentIntegralClasses F (t + 1) A,
            f (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
              (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out))
            ∂whittakerQuotientMeasure F (t + 1) =
        _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.localTerm
            (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a b s lam *
          ∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1) := by
    intro lam
    have hcell : ∫ q in unipotentIntegralClasses F (t + 1) A,
          f (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
            (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out))
          ∂whittakerQuotientMeasure F (t + 1) =
        ∫ q in unipotentIntegralClasses F (t + 1) A,
          cellFactor h v ψv a b s (torus (placeUniformizer v) lam) * f q
          ∂whittakerQuotientMeasure F (t + 1) :=
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) A) fun q hq =>
        integrand_shift ψ hψ h hTd hTd' Pd Pd' hPd hPd' hx hx' hv hψv h0 ha hb s lam hvA hq
    rw [hcell, integral_const_mul, ← mul_assoc, zpow_modulusExponent_mul_cellFactor h v h0]
  have e : ∫ q in unipotentIntegralClasses F (t + 1) (insert v A), f q
      ∂whittakerQuotientMeasure F (t + 1) =
      L * ∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1) := by
    refine hsum.unique ?_
    have h2 := hL.mul_right
      (∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1))
    convert h2 using 1
    funext lam
    exact hterm lam
  rw [Finset.cons_eq_insert]
  convert e using 4

end Step

/-! ### The reduction -/

/-- **The reduction.** `UnequalDualEulerFactorizationStatement` follows from the unfolding
statement `UnequalUnfoldingStatement`. -/
theorem unequalDualEulerFactorization_of_unfolding (hU : UnequalUnfoldingStatement.{u}) :
    UnequalDualEulerFactorizationStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hψS
  obtain ⟨C, -, hC⟩ := hU F r t h T T'
  obtain ⟨σE, hσE⟩ := exists_partialEulerFactor_convergence Pd Pd' hPd hPd'
  obtain ⟨Ab, hAb⟩ := exists_hasSatakeBound_presentation Td Pd
  obtain ⟨Bb, hBb⟩ := exists_hasSatakeBound_presentation Td' Pd'
  obtain ⟨σC, hσC⟩ :=
    _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.exists_hasSum_localTerm h Ab Bb
  refine ⟨max (1 + C) (max σE σC), fun x x' hx hx' => ?_⟩
  intro Wdual W'dual s hs
  have hs1 : 1 + C < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsE : σE < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsC : σC < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hconv : DualWhittakerAbsolutelyConvergent F h Wdual W'dual s := by
    have h1 : (1 - s).re < -C := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h2 := ((hC ψ.complex hstd x x').2 (1 - s) h1).1
    rwa [sub_sub_cancel] at h2
  obtain ⟨hsumE, hprod⟩ := hσE s hsE
  refine ⟨hconv, hsumE, _, hprod, ?_⟩
  suffices hstep : ∀ A : Finset (FinitePlace F), S ⊆ A → ∀ v : {v : FinitePlace F // v ∉ S},
      ∀ hv : v.1 ∉ A,
      ∫ q in unipotentIntegralClasses F (t + 1) (Finset.cons v.1 A hv),
          dualWhittakerIntegrand F h Wdual W'dual s q ∂whittakerQuotientMeasure F (t + 1) =
        partialEulerFactor Pd Pd' hPd hPd' v s *
          ∫ q in unipotentIntegralClasses F (t + 1) A,
            dualWhittakerIntegrand F h Wdual W'dual s q ∂whittakerQuotientMeasure F (t + 1) by
    have key := integral_eq_hasProd_mul_setIntegral hconv.2.2 hprod hstep
    rw [dualWhittakerIntegral, key, partialDualWhittakerIntegral, mul_comm]
    rfl
  intro A hSA v hvA
  obtain ⟨ψv, hψv, h0⟩ := hψS v.1 v.2
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (Pd.spectralSystem.eigenvalues v.1 (fun hvP => v.2 (hPd hvP)))
  obtain ⟨b, hb⟩ := Unramified.Eigenvalues.ofTuple_surjective (t + 1)
    (Pd'.spectralSystem.eigenvalues v.1 (fun hvP => v.2 (hPd' hvP)))
  have hq1 : 1 < (CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality :=
    lt_of_lt_of_le one_lt_two (CuspidalPairEulerConvergence.two_le_residueCardinality v.1)
  have hab : ∀ i, ‖(a i : ℂ)‖ ≤
      ((CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality : ℝ) ^ Ab :=
    fun i => hAb v.1 (fun hvP => v.2 (hPd hvP)) (a i) (by rw [← ha]; exact mem_ofTuple a i)
  have hbb : ∀ j, ‖(b j : ℂ)‖ ≤
      ((CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality : ℝ) ^ Bb :=
    fun j => hBb v.1 (fun hvP => v.2 (hPd' hvP)) (b j) (by rw [← hb]; exact mem_ofTuple b j)
  obtain ⟨-, hL⟩ := hσC _ hq1 a b hab hbb s hsC
  rw [partialEulerFactor_eq hPd hPd' v ha hb s]
  exact setIntegral_cons_eq ψ hψ h hTd hTd' Pd Pd' hPd hPd' hx hx' v.2 hψv h0 ha hb s hL
    hconv.2.2 hvA

/-- The reduction as a proposition: `UnequalUnfoldingStatement` implies
`UnequalDualEulerFactorizationStatement`. -/
def UnequalDualEulerFactorizationUnfoldingReductionStatement : Prop :=
  UnequalUnfoldingStatement.{u} → UnequalDualEulerFactorizationStatement.{u, uQ}

theorem unequalDualEulerFactorizationUnfoldingReduction :
    UnequalDualEulerFactorizationUnfoldingReductionStatement.{u, uQ} :=
  fun hU => unequalDualEulerFactorization_of_unfolding hU

end Langlands.Global.RankinSelbergGlobal.UnequalDualEulerContragredient
