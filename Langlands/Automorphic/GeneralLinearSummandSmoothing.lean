import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction
import Langlands.Automorphic.GroupSchemeQuotientL2IntegratedRepresentative
import Langlands.Automorphic.GeneralLinearCuspidalFormClassDerivativeProof
import Langlands.Global.ArchimedeanConvolutionDifferentiationProof
import Langlands.Global.ArchimedeanEnvelopingSupportProof
import Langlands.Analysis.NormalizedAverageApproximation

/-! # Archimedean smoothing of a continuous quotient class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic ContinuousRationalFunctions

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

section Smoothing

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))

local notation "n" => r + 1
local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "Γ" => positiveRationalSubgroup F GLs T i
local notation "Q" => PositiveRationalQuotient F GLs T i
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F n

/-- The archimedean inclusion into the group-scheme adelic points. -/
def archimedeanAdelicPoint : C(InfiniteAdelicGL F n, AdelicGroupPoints F GLs) :=
  ⟨fun z => (m).symm (AdelicGL.ofInfinite F n z),
    (m).symm.continuous.comp (AdelicGL.ofInfinite F n).continuous⟩

/-- The weight `z ↦ (D κ)(z⁻¹)` of the differentiated kernel. -/
def smoothingWeight (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) : C(InfiniteAdelicGL F n, ℂ) :=
  ⟨fun z => (ArchimedeanGL.envelopingAction F n D κ.val).val z⁻¹,
    (ArchimedeanGL.continuous F n _).comp continuous_inv⟩

theorem smoothingWeight_hasCompactSupport (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) :
    HasCompactSupport (smoothingWeight F r D κ) :=
  (ArchimedeanGL.envelopingCompactSupport F n D κ.val κ.property).comp_homeomorph
    (Homeomorph.inv (InfiniteAdelicGL F n))

theorem evaluate_pullback (k : C(Q, ℂ)) (g : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n (continuousGeneralLinearEquiv F n
      (positiveQuotientContinuousPullback F GLs T i k)) g =
      k (LeftCosetSpace.mk Γ ((m).symm g)) := by
  rw [evaluate_continuousGeneralLinearEquiv]
  rfl

variable [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  (ν : Measure (InfiniteAdelicGL F (r + 1))) [ν.IsHaarMeasure]

/-- The smoothed continuous function on the quotient attached to an enveloping element. -/
def smoothedQuotientFunction (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (h : C(Q, ℂ)) : C(Q, ℂ) :=
  weightedQuotientOrbitIntegral F GLs T i ν (archimedeanAdelicPoint F r) (smoothingWeight F r D κ)
    (smoothingWeight_hasCompactSupport F r D κ) h

/-- The pointwise slice formula: the smoothed function is a right convolution in the
archimedean variable of the original slice with the differentiated kernel. -/
theorem evaluate_smoothedQuotientFunction (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (h : C(Q, ℂ))
    (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n (continuousGeneralLinearEquiv F n
      (positiveQuotientContinuousPullback F GLs T i (smoothedQuotientFunction F r T i ν D κ h)))
        (AdelicGL.pair F n a b) =
      ∫ y, ContinuousRationalFunctions.evaluate F n (continuousGeneralLinearEquiv F n
          (positiveQuotientContinuousPullback F GLs T i h)) (AdelicGL.pair F n y b) *
        (ArchimedeanGL.envelopingAction F n D κ.val).val (y⁻¹ * a) ∂ν := by
  rw [evaluate_pullback, smoothedQuotientFunction, weightedQuotientOrbitIntegral_apply]
  let s : InfiniteAdelicGL F n → ℂ := fun y =>
    ContinuousRationalFunctions.evaluate F n (continuousGeneralLinearEquiv F n
      (positiveQuotientContinuousPullback F GLs T i h)) (AdelicGL.pair F n y b) *
        (ArchimedeanGL.envelopingAction F n D κ.val).val (y⁻¹ * a)
  rw [← integral_mul_left_eq_self s a]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [s, evaluate_pullback]
  have hProd : (m).symm (AdelicGL.pair F n (a * z) b) =
      (m).symm (AdelicGL.pair F n a b) * archimedeanAdelicPoint F r z := by
    change _ = _ * (m).symm (AdelicGL.ofInfinite F n z)
    rw [← map_mul, AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]
  rw [LeftCosetSpace.rightTranslate_mk, ← hProd, mul_inv_rev, inv_mul_cancel_right, mul_comm]
  rfl


omit [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))] in
theorem ofFinite_mul_ofInfinite (l : FiniteAdelicGL F n) (z : InfiniteAdelicGL F n) :
    AdelicGL.ofFinite F n l * AdelicGL.ofInfinite F n z =
      AdelicGL.ofInfinite F n z * AdelicGL.ofFinite F n l := by
  simp only [AdelicGL.ofFinite_eq_pair, AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, one_mul,
    mul_one]

/-- If the continuous function is invariant under right translation by an open subgroup of the
finite adelic points, so is every smoothed function, because finite and archimedean
translations commute. -/
theorem smoothedQuotientFunction_rightTranslate_finite (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (h : C(Q, ℂ)) (L : Subgroup (FiniteAdelicGL F n))
    (hL : ∀ l : L, ∀ q, h (LeftCosetSpace.rightTranslate Γ
      ((m).symm (AdelicGL.ofFinite F n l)) q) = h q) (l : L) (q : Q) :
    smoothedQuotientFunction F r T i ν D κ h
        (LeftCosetSpace.rightTranslate Γ ((m).symm (AdelicGL.ofFinite F n l)) q) =
      smoothedQuotientFunction F r T i ν D κ h q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  simp only [smoothedQuotientFunction, weightedQuotientOrbitIntegral_apply,
    LeftCosetSpace.rightTranslate_mk]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  have hcomm : x * (m).symm (AdelicGL.ofFinite F n l) * archimedeanAdelicPoint F r z =
      x * archimedeanAdelicPoint F r z * (m).symm (AdelicGL.ofFinite F n l) := by
    change x * (m).symm _ * (m).symm _ = x * (m).symm _ * (m).symm _
    rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul, ofFinite_mul_ofInfinite]
  dsimp only
  rw [hcomm, ← LeftCosetSpace.rightTranslate_mk, hL l]

omit [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))] in
private theorem continuousRationalFunctions_ext
    {f g : Langlands.Automorphic.ContinuousRationalFunctions F n}
    (h : ∀ a b, ContinuousRationalFunctions.evaluate F n f (AdelicGL.pair F n a b) =
      ContinuousRationalFunctions.evaluate F n g (AdelicGL.pair F n a b)) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx := h (AdelicGL.infinite F n x) (AdelicGL.finite F n x)
  rwa [AdelicGL.pair_projections] at hx

/-- **Archimedean smoothing.** Convolving a continuous quotient function, invariant under an
open subgroup of the finite adelic points, with a smooth compactly supported archimedean kernel
gives a finite-smooth rational function. Its enveloping derivatives are the smoothings with the
differentiated kernels. -/
theorem exists_finiteSmooth_smoothing (κ : ArchimedeanGL.SmoothCompactKernel F n) (h : C(Q, ℂ))
    (L : OpenSubgroup (FiniteAdelicGL F n))
    (hL : ∀ l : L.toSubgroup, ∀ q, h (LeftCosetSpace.rightTranslate Γ
      ((m).symm (AdelicGL.ofFinite F n l)) q) = h q) :
    ∃ f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n, ∀ D : ArchimedeanGL.EnvelopingAlgebra F n,
      (finiteSmoothEnvelopingAction F n D f).val = continuousGeneralLinearEquiv F n
        (positiveQuotientContinuousPullback F GLs T i (smoothedQuotientFunction F r T i ν D κ h)) := by
  let g₀ := continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLs T i h)
  let s (b : FiniteAdelicGL F n) : C(InfiniteAdelicGL F n, ℂ) :=
    ⟨fun y => ContinuousRationalFunctions.evaluate F n g₀ (AdelicGL.pair F n y b),
      (ContinuousRationalFunctions.continuous_evaluate F n g₀).comp
        ((AdelicGL.continuous_pair F n).comp (continuous_id.prodMk continuous_const))⟩
  have hconv := fun b => ArchimedeanGL.compactKernelConvolutionDifferentiation F n ν (s b) κ
  choose Fb hFb hDb using hconv
  let fD (D : ArchimedeanGL.EnvelopingAlgebra F n) := continuousGeneralLinearEquiv F n
    (positiveQuotientContinuousPullback F GLs T i (smoothedQuotientFunction F r T i ν D κ h))
  have hEval (D : ArchimedeanGL.EnvelopingAlgebra F n) (a b) :
      ContinuousRationalFunctions.evaluate F n (fD D) (AdelicGL.pair F n a b) =
        (ArchimedeanGL.envelopingAction F n D (Fb b)).val a := by
    rw [hDb b D a, evaluate_smoothedQuotientFunction]
    rfl
  have hslice (b : FiniteAdelicGL F n) :
      Langlands.Automorphic.infiniteSlice F n b (fD 1) = (Fb b).val := by
    funext a
    change ContinuousRationalFunctions.evaluate F n (fD 1) (AdelicGL.pair F n a b) = _
    rw [hEval, map_one, Module.End.one_apply]
  have hsmooth : fD 1 ∈ (Langlands.Automorphic.infiniteSmoothSubrepresentation F n).toSubmodule := by
    change fD 1 ∈ ⨅ b : FiniteAdelicGL F n,
      (ArchimedeanGL.smoothFunctions F n).comap (Langlands.Automorphic.infiniteSlice F n b)
    refine Submodule.mem_iInf _ |>.mpr fun b => ?_
    rw [Submodule.mem_comap, hslice]
    exact (Fb b).property
  have hlevel : fD 1 ∈ (Langlands.Automorphic.finiteSmoothSubrepresentation F n).toSubmodule := by
    refine ⟨L, fun l => ?_⟩
    apply continuousRationalFunctions_ext F r
    intro a b
    change ContinuousRationalFunctions.evaluate F n (fD 1)
      (AdelicGL.pair F n a b * AdelicGL.ofFinite F n l) = _
    simp only [fD, evaluate_pullback]
    rw [map_mul, ← LeftCosetSpace.rightTranslate_mk,
      smoothedQuotientFunction_rightTranslate_finite F r T i ν 1 κ h L.toSubgroup hL l]
  let f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n := ⟨fD 1, hsmooth, hlevel⟩
  refine ⟨f, fun D => ?_⟩
  apply continuousRationalFunctions_ext F r
  intro a b
  have hfs : finiteSmoothSlice F n b f = Fb b := by
    apply Subtype.ext
    exact hslice b
  rw [evaluate_finiteSmoothEnvelopingAction, hEval, hfs]


section L2

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc

/-- The `L²` smoothing of a class by the differentiated kernel: the Bochner integral of its
archimedean orbit against `z ↦ (D κ)(z⁻¹)`. -/
def smoothedClass (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (u : Lp ℂ 2 μQ) : Lp ℂ 2 μQ :=
  ∫ z, smoothingWeight F r D κ z • ρ (archimedeanAdelicPoint F r z) u ∂ν

variable [SecondCountableTopology (InfiniteAdelicGL F (r + 1))]

theorem integrable_smoothingOrbit (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (u : Lp ℂ 2 μQ) (h : C(Q, ℂ))
    (hrep : (u : Q → ℂ) =ᵐ[μQ] h) :
    Integrable (fun z => smoothingWeight F r D κ z • ρ (archimedeanAdelicPoint F r z) u) ν :=
  (groupSchemeQuotientL2IntegratedRepresentative F GLs T i hi I e hc ν
    (archimedeanAdelicPoint F r) (smoothingWeight F r D κ)
    (smoothingWeight_hasCompactSupport F r D κ) u h hrep).1

/-- The smoothed class is the class of the smoothed continuous function. -/
theorem isGeneralLinearFormClass_smoothedClass (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (u : Lp ℂ 2 μQ) (h : C(Q, ℂ))
    (hrep : (u : Q → ℂ) =ᵐ[μQ] h) :
    IsGeneralLinearFormClass F r T i (smoothedClass F r T i ν hi I e hc D κ u)
      (continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLs T i
        (smoothedQuotientFunction F r T i ν D κ h))) :=
  ⟨smoothedQuotientFunction F r T i ν D κ h, rfl,
    (groupSchemeQuotientL2IntegratedRepresentative F GLs T i hi I e hc ν
      (archimedeanAdelicPoint F r) (smoothingWeight F r D κ)
      (smoothingWeight_hasCompactSupport F r D κ) u h hrep).2⟩

omit [BorelSpace (InfiniteAdelicGL F (r + 1))] [ν.IsHaarMeasure]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
/-- Smoothing a class of a closed invariant submodule stays in it. -/
theorem smoothedClass_mem (A : Submodule ℂ (Lp ℂ 2 μQ)) (hA : IsClosed (A : Set (Lp ℂ 2 μQ)))
    (hInv : ∀ a, ∀ φ ∈ A, ρ a φ ∈ A) (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) {u : Lp ℂ 2 μQ} (hu : u ∈ A)
    (hint : Integrable (fun z => smoothingWeight F r D κ z • ρ (archimedeanAdelicPoint F r z) u) ν) :
    smoothedClass F r T i ν hi I e hc D κ u ∈ A :=
  Langlands.Analysis.NormalizedAverage.integral_mem_of_isClosed A hA hint
    fun _ => A.smul_mem _ (hInv _ u hu)

omit [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem smoothingWeight_add (D₁ D₂ : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (z : InfiniteAdelicGL F n) :
    smoothingWeight F r (D₁ + D₂) κ z = smoothingWeight F r D₁ κ z + smoothingWeight F r D₂ κ z := by
  change (ArchimedeanGL.envelopingAction F n (D₁ + D₂) κ.val).val z⁻¹ = _
  rw [map_add, LinearMap.add_apply]
  rfl

omit [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem smoothingWeight_smul (c : ℂ) (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (z : InfiniteAdelicGL F n) :
    smoothingWeight F r (c • D) κ z = c * smoothingWeight F r D κ z := by
  change (ArchimedeanGL.envelopingAction F n (c • D) κ.val).val z⁻¹ = _
  rw [map_smul, LinearMap.smul_apply]
  rfl

theorem smoothedClass_add (D₁ D₂ : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (u : Lp ℂ 2 μQ) (h : C(Q, ℂ))
    (hrep : (u : Q → ℂ) =ᵐ[μQ] h) :
    smoothedClass F r T i ν hi I e hc (D₁ + D₂) κ u =
      smoothedClass F r T i ν hi I e hc D₁ κ u + smoothedClass F r T i ν hi I e hc D₂ κ u := by
  rw [smoothedClass, smoothedClass, smoothedClass, ← integral_add
    (integrable_smoothingOrbit F r T i ν hi I e hc D₁ κ u h hrep)
    (integrable_smoothingOrbit F r T i ν hi I e hc D₂ κ u h hrep)]
  congr 1
  funext z
  rw [smoothingWeight_add, add_smul]

omit [BorelSpace (InfiniteAdelicGL F (r + 1))] [ν.IsHaarMeasure]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem smoothedClass_smul (c : ℂ) (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (u : Lp ℂ 2 μQ) :
    smoothedClass F r T i ν hi I e hc (c • D) κ u =
      c • smoothedClass F r T i ν hi I e hc D κ u := by
  rw [smoothedClass, smoothedClass, ← integral_smul]
  congr 1
  funext z
  rw [smoothingWeight_smul, mul_smul]

/-- **Differentiation of smoothed classes.** For a class with a continuous representative
invariant under an open subgroup of the finite adelic points, the orbit of the smoothed class
along a real exponential curve has derivative at `0` equal to the smoothing with the kernel
differentiated by the corresponding generator. -/
theorem hasDerivAt_smoothedClass (κ : ArchimedeanGL.SmoothCompactKernel F n) (u : Lp ℂ 2 μQ)
    (h : C(Q, ℂ)) (hrep : (u : Q → ℂ) =ᵐ[μQ] h) (L : OpenSubgroup (FiniteAdelicGL F n))
    (hL : ∀ l : L.toSubgroup, ∀ q, h (LeftCosetSpace.rightTranslate Γ
      ((m).symm (AdelicGL.ofFinite F n l)) q) = h q)
    (X : ArchimedeanGL.RealLieAlgebra F n) (D : ArchimedeanGL.EnvelopingAlgebra F n) :
    HasDerivAt (fun t : ℝ => ρ (GeneralLinearFormClassDerivative.exponentialAdelicPoint F r X t)
        (smoothedClass F r T i ν hi I e hc D κ u))
      (smoothedClass F r T i ν hi I e hc
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X) * D) κ u) 0 := by
  obtain ⟨f, hf⟩ := exists_finiteSmooth_smoothing F r T i ν κ h L hL
  have hφ := isGeneralLinearFormClass_smoothedClass F r T i ν hi I e hc D κ u h hrep
  rw [← hf D] at hφ
  have hψ := isGeneralLinearFormClass_smoothedClass F r T i ν hi I e hc
    (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X) * D) κ u h hrep
  rw [← hf, map_mul, Module.End.mul_apply] at hψ
  exact GeneralLinearFormClassDerivative.quotient_hasDerivAt_of_formClasses F r T i hi I e hc X
    (finiteSmoothEnvelopingAction F n D f) _ _ hφ hψ

end L2

end Smoothing

end Langlands.Automorphic.GroupSchemeFunctions
