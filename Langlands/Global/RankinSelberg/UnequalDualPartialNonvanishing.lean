import Langlands.Global.RankinSelberg.ContragredientDualSplit
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition

/-! # Passing dual nonvanishing to the integral classes -/

noncomputable section

open NumberField MeasureTheory Filter
open scoped Classical CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.UnequalDualPartial

open Langlands.Automorphic Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa
open Langlands.GeneralLinear.Spherical Langlands.GeneralLinear.RectangularSupport
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open LocalPointFactorization UnequalDualEuler ContragredientDualSplit

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

private theorem dualSplit {r : ℕ} {T : CuspidalOperatorRealization F r}
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ z : F, ψ (algebraMap F (Adeles F) z) = 1)
    (P : CuspidalSpectralPresentation.{u,uQ} T) {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP))) :
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ k : FiniteLocalGL F (r + 1) v,
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) (g * localPoint F (r + 1) v k) =
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g * sphInv v ψv r a⁻¹ k) ∧
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ k : FiniteLocalGL F (r + 1) v,
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex⁻¹ x) (g * localPoint F (r + 1) v k) =
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex⁻¹ x) g * sphStd v ψv r a⁻¹ k) := by
  obtain ⟨hs, hsi⟩ := whittaker_split UnramifiedWhittaker.unramifiedWhittakerFactorization
    ψ hψ hP hS hx hv hψv ha
  constructor
  · intro g hg k
    rw [dualFunction_mul_localPoint F v hs (sphStd_weylLong h0 r a) hg]
    simpa only [inv_inv] using congrArg (_ * ·)
      (sphStd_inv_weylLong_mul_inverseTranspose h0 r a⁻¹ k)
  · intro g hg k
    rw [dualFunction_mul_localPoint F v hsi (sphInv_weylLong h0 r a) hg]
    simpa only [inv_inv] using congrArg (_ * ·)
      (sphInv_inv_weylLong_mul_inverseTranspose h0 r a⁻¹ k)

variable {r t : ℕ} (h : t < r) {T : CuspidalOperatorRealization F r}
  {T' : CuspidalOperatorRealization F t}
  (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
  (hψ : ∀ z : F, ψ (algebraMap F (Adeles F) z) = 1)
  (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
  {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
  (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
  {x : T.Space} {x' : T'.Space} (hx : IsSphericalOutside F T S x)
  (hx' : IsSphericalOutside F T' S x')

local notation "Wd" => Unfolding.dualWhittaker F h T ψ.complex x
local notation "Vd" => dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')

include hψ P P' hP hP' hS hx hx' in
private theorem dualKernel_shift (s : ℂ) (v : FinitePlace F) (hv : v ∉ S)
    (lam : Fin (t + 1) → ℤ) :
    ∃ c : ℂ, ∀ g : Points F (t + 1),
      IsUnipotentIntegral F (t + 1) v (finiteComponent F (t + 1) v g) →
      Unfolding.dualKernel F h Wd Vd s
        (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * g) =
        c * Unfolding.dualKernel F h Wd Vd s g := by
  obtain ⟨ψv, hψv, h0⟩ := hS v hv
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
  obtain ⟨b, hb⟩ := Unramified.Eigenvalues.ofTuple_surjective (t + 1)
    (P'.spectralSystem.eigenvalues v (fun hvP => hv (hP' hvP)))
  have hsplit := (dualSplit ψ hψ P hP hS hx hv hψv h0 ha).1
  have hsplit' := (dualSplit ψ hψ P' hP' hS hx' hv hψv h0 hb).2
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  let Q := torus (placeUniformizer v) lam
  refine ⟨cellFactor h v ψv a⁻¹ b⁻¹ s Q, fun g hg => ?_⟩
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hN (n : unipotentAdelic F (t + 1)) (y : Points F (t + 1)) :
      Unfolding.dualKernel F h Wd Vd s (n.val * y) = Unfolding.dualKernel F h Wd Vd s y :=
    Unfolding.dualKernel_whittaker_unipotent_mul F h T T' ψ.complex hstd x x' s n y
  obtain ⟨u, hu, k, hk, hgv⟩ := exists_eq_mul_of_isUnipotentIntegral v hg
  obtain ⟨g₁, rfl⟩ : ∃ g₁, g = localPoint F (t + 1) v u * g₁ :=
    ⟨(localPoint F (t + 1) v u)⁻¹ * g, by group⟩
  have hg₁ : finiteComponent F (t + 1) v g₁ = k := by
    rw [finiteComponent_mul, finiteComponent_localPoint] at hgv
    exact mul_left_cancel hgv
  have hgK : finiteComponent F (t + 1) v g₁ ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t := hg₁.symm ▸ hk
  have e : localPoint F (t + 1) v Q * (localPoint F (t + 1) v u * g₁) =
      localPoint F (t + 1) v (Q * u * Q⁻¹) * (localPoint F (t + 1) v Q * g₁) := by
    rw [← mul_assoc (localPoint F (t + 1) v (Q * u * Q⁻¹)), ← localPoint_mul,
      inv_mul_cancel_right, localPoint_mul, mul_assoc]
  rw [e, hN ⟨_, localPoint_mem_unipotentAdelic F v
    (torus_mul_mul_inv_mem _ lam hu)⟩, hN ⟨_, localPoint_mem_unipotentAdelic F v hu⟩]
  have hrect :
      Unfolding.dualRectIntegral F h Wd (localPoint F (t + 1) v Q * g₁) =
        sphInv v ψv r a⁻¹ (rectGL h Q 0) * Unfolding.dualRectIntegral F h Wd g₁ := by
    have he y : Wd (rectangularPoint F h (localPoint F (t + 1) v Q * g₁) y) =
        sphInv v ψv r a⁻¹ (rectGL h Q 0) * Wd (rectangularPoint F h g₁ y) := by
      unfold Unfolding.dualWhittaker translateFunction
      rw [Unfolding.rectangularPoint_mul_left, pad_localPoint F h, mul_assoc]
      refine apply_localPoint_mul_of_split v hsplit _ _ ?_
      rw [finiteComponent_mul, finiteComponent_rectangularPoint F h]
      exact sphericalWhittaker_inverseStandard_rectGL_zero_mul h (isUniformizingElement_canonical v)
        (integer_trivial_of_conductor h0) (exists_ne_one_of_conductor h0)
        _ a⁻¹ Q hgK _ (finiteComponent_unfoldingWeyl_mem h v)
    unfold Unfolding.dualRectIntegral
    simp_rw [he]
    exact integral_const_mul _ _
  have hvd : Vd (localPoint F (t + 1) v Q * g₁) = sphStd v ψv t b⁻¹ Q * Vd g₁ := by
    refine apply_localPoint_mul_of_split v hsplit' Q g₁ ?_
    have ht := isIntegrallyTrivial_standardCharacter (integer_trivial_of_conductor h0) t
    unfold sphStd
    rw [sphericalWhittaker_mul_integral _ _ _ ht Q hgK]
    have h1 := sphericalWhittaker_mul_integral (isUniformizingElement_canonical v)
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality b⁻¹ ht 1 hgK
    rw [one_mul, sphericalWhittaker_one _ _ _ ht] at h1
    rw [h1, mul_one]
  unfold Unfolding.dualKernel
  rw [hrect, hvd, detPower_localPoint_mul, cellFactor]
  ring

include hψ P P' hP hP' hS hx hx' in
/-- If the outer dual Whittaker integrand is integrable, a nonzero full integral
forces a nonzero partial integral on the classes integral outside the finite set. -/
theorem partialDualWhittakerIntegral_ne_zero (s : ℂ)
    (hint : Integrable (dualWhittakerIntegrand F h Wd Vd s)
      (whittakerQuotientMeasure F (t + 1)))
    (hglobal : dualWhittakerIntegral F h Wd Vd s ≠ 0) :
    partialDualWhittakerIntegral F h S Wd Vd s ≠ 0 := by
  intro hpartial
  let f := dualWhittakerIntegrand F h Wd Vd s
  let measure := whittakerQuotientMeasure F (t + 1)
  let I (A : Finset (FinitePlace F)) := ∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂measure
  have hbase : I S = 0 := by
    rw [partialDualWhittakerIntegral_eq_setIntegral] at hpartial
    exact hpartial
  have hstep (A : Finset (FinitePlace F)) (hSA : S ⊆ A) (v : FinitePlace F) (hvA : v ∉ A)
      (hA : I A = 0) : I (insert v A) = 0 := by
    obtain ⟨-, hsum⟩ := whittakerCellDecomposition F (t + 1) A v hvA (placeUniformizer v)
      (isUniformizingElement_valued v) f hint
    have hcell (lam : Fin (t + 1) → ℤ) :
        ∃ c : ℂ, ∀ q ∈ unipotentIntegralClasses F (t + 1) A,
          f (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
            (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out)) = c * f q := by
      obtain ⟨c, hc⟩ := dualKernel_shift h ψ hψ P P' hP hP' hS hx hx' s v
        (fun hvS => hvA (hSA hvS)) lam
      refine ⟨c, fun q hq => ?_⟩
      dsimp only [f]
      rw [Unfolding.dualWhittakerIntegrand_eq, Unfolding.dualWhittakerIntegrand_eq]
      obtain ⟨n, hn⟩ := Unfolding.exists_out_mk_eq (unipotentAdelic F (t + 1))
        (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out)
      rw [hn, Unfolding.dualKernel_whittaker_unipotent_mul F h T T' ψ.complex
        (isStandardAdditiveCharacter_of_unitary ψ hψ) x x' s n]
      exact hc q.out ((show q.out ∈ unipotentIntegralOutside F (t + 1) A from hq) v hvA)
    refine hsum.unique ?_
    convert (hasSum_zero : HasSum (fun _ : Fin (t + 1) → ℤ => (0 : ℂ)) 0) using 1
    funext lam
    obtain ⟨c, hc⟩ := hcell lam
    rw [setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) A) hc,
      integral_const_mul]
    change _ * (c * I A) = 0
    rw [hA, mul_zero, mul_zero]
  have hzero (B : Finset (FinitePlace F)) : I (S ∪ B) = 0 := by
    induction B using Finset.induction_on with
    | empty => simpa only [Finset.union_empty] using hbase
    | insert v B hv ih =>
      rw [Finset.union_insert]
      by_cases hvS : v ∈ S
      · rwa [Finset.insert_eq_of_mem (Finset.mem_union_left _ hvS)]
      · exact hstep _ Finset.subset_union_left v
          (by simpa only [Finset.mem_union, not_or] using And.intro hvS hv) ih
  let : Countable (FinitePlace F) := finitePlace_countable F
  have hlim := tendsto_setIntegral_of_monotone
    (fun A : Finset (FinitePlace F) => measurableSet_unipotentIntegralClasses (t + 1) A)
    (fun A B (hab : A ⊆ B) => unipotentIntegralClasses_mono hab) hint.integrableOn
  rw [iUnion_unipotentIntegralClasses (t + 1), Measure.restrict_univ] at hlim
  have hzero' : ∀ᶠ A : Finset (FinitePlace F) in atTop, I A = 0 := by
    filter_upwards [eventually_ge_atTop S] with A hSA
    simpa only [Finset.union_eq_right.mpr hSA] using hzero A
  exact hglobal (tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hzero')

end Langlands.Global.RankinSelbergGlobal.UnequalDualPartial
