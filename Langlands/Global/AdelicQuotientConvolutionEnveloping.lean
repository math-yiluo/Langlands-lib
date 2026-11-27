import Langlands.Global.AdelicArchimedeanKernelLift
import Langlands.Automorphic.GroupSchemePositiveQuotientL2Smoothing
import Langlands.Representation.Archimedean.GardingDensity
import Langlands.Representation.Archimedean.GardingFunctionals
import Langlands.Representation.Archimedean.SmoothVectorEnvelopingAction

/-! # Derivatives of convolution representatives on the positive rational quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme Langlands.Archimedean
open AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (J : Type) [Fintype J] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "M" => InfiniteAdelicGroupPoints F G
local notation "B" => FiniteAdelicGroupPoints F G
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dm" => (Measure.haar : Measure M)
local notation "I" => 𝓘(ℝ, smoothModel F d)
local notation "ιi" => ContinuousMonoidHom.toMonoidHom (ofInfinite F G)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : AdelicGroupPoints F G →* (H →L[ℂ] H))
  (j : H →L[ℂ] Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))
  (hπ : IsContinuousRepresentation π)
  (hj : ∀ g u, j (π g u) = haarQuotientL2BoundedRightAction F G T i hi J e hc g (j u))

include hi J e hc hπ hj in
/-- The actual smooth quotient representative differentiates by the same kernel as the
Hilbert-space orbit. This applies to every element of the complex enveloping algebra. -/
theorem exists_convolution_enveloping_representative (L : Subgroup B)
    (hLo : IsOpen (L : Set B)) (hLc : IsCompact (L : Set B))
    (u : H) (hLu : ∀ l ∈ L, π (ofFinite F G l) u = u)
    (h : M → ℂ) (hhk : HasCompactSupport h) (w : H)
    (hw_eq : w = ∫ x, h x • π (ofInfinite F G x) u ∂dm) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
    let φ := positiveQuotientLpSmoothing T i (liftArchimedeanKernel L h) (j u)
    ContMDiff I 𝓘(ℝ, ℂ) ∞ h → ∀ (hφ : IsAdelicSmoothFunction F G φ),
    ∃ hw : Langlands.Archimedean.IsSmoothVector I (π.comp ιi) w,
    ∀ D : AdelicEnvelopingAlgebra F G hsmooth,
      ∃ ψ : A → ℂ, Continuous ψ ∧ IsLeftInvariantUnder F G Γ ψ ∧
        ((j (SmoothVectorEnveloping.envelopingAction (π.comp ιi) hcalc D ⟨w, hw⟩) : Q → ℂ)
          =ᵐ[dq] fun q => ψ q.out) ∧
        ∀ b : B, ((plotSmoothEnvelopingAction F G hsmooth hcalc D
          ⟨functionInfiniteSlice F G φ b, hφ.2.1 b⟩ : InfinitePlotSmoothFunctions F G) : M → ℂ) =
          functionInfiniteSlice F G ψ b := by
  classical
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  let φ := positiveQuotientLpSmoothing T i (liftArchimedeanKernel L h) (j u)
  subst w
  dsimp only
  intro hhd hφ
  let := positiveRationalQuotient_borelSpace F G T i hi J e hc
  let R := π.comp ιi
  have hR : IsContinuousRepresentation R := hπ.comp
    (((ofInfinite F G).continuous.comp continuous_fst).prodMk continuous_snd)
  let Ck := smoothCompactKernels (smoothModel F d) M
  have hOrb (k : Ck) : Integrable (fun x => k.val x • R x u) dm :=
    (k.property.1.continuous.smul (hR.comp (continuous_id.prodMk continuous_const)))
      |>.integrable_of_hasCompactSupport k.property.2.smul_right
  let vector (k : Ck) : Langlands.Archimedean.smoothVectors I R :=
    ⟨∫ x, k.val x • R x u ∂dm, isSmoothVector_gardingIntegral dm R hR k.val k.property.1 k.property.2 u⟩
  have hVector_add (k k' : Ck) : vector (k + k') = vector k + vector k' := by
    apply Subtype.ext
    simp only [vector, Submodule.coe_add, Pi.add_apply, add_smul]
    exact integral_add (hOrb k) (hOrb k')
  have hVector_smul (c : ℂ) (k : Ck) : vector (c • k) = c • vector k := by
    apply Subtype.ext
    change (∫ x, (c * k.val x) • R x u ∂dm) = c • ∫ x, k.val x • R x u ∂dm
    simp only [mul_smul, integral_smul]
  let out (k : Ck) := positiveQuotientLpSmoothing T i (liftArchimedeanKernel L k.val) (j u)
  have hTest (k : Ck) : IsAdelicTestFunction F G (liftArchimedeanKernel L k.val) :=
    liftArchimedeanKernel_isTestFunction hsmooth L hLo hLc k.val k.property.2 k.property.1
  let base := (j u : Q → ℂ) ∘ LeftCosetSpace.mk Γ
  have hbase : Measurable base :=
    (Lp.stronglyMeasurable (j u)).measurable.comp (LeftCosetSpace.measurable_mk Γ)
  have hloc := locallyIntegrable_positiveQuotientLpPullback T i hi J e hc (j u)
  have hdiff (k : Ck) := adelicRightConvolutionDifferentiation F G d hsmooth _ base (hTest k) hbase hloc
  have hout (k : Ck) : IsAdelicSmoothFunction F G (out k) := (hdiff k).2.1
  have hae (k : Ck) : (j (vector k) : Q → ℂ) =ᵐ[dq] fun q => out k q.out := by
    have hOrbc : Continuous fun x : A => π x u := hπ.comp (continuous_id.prodMk continuous_const)
    have hconv := integral_liftArchimedeanKernel π L hLo hLc k.val k.property.1.continuous k.property.2 u hOrbc hLu
    let f := liftArchimedeanKernel L k.val
    have hfi : Integrable f dg := (hTest k).1.1.integrable_of_hasCompactSupport (hTest k).2.1
    have hv : j (vector k) = haarQuotientL2IntegratedAction F G T i hi J e hc dg f hfi (j u) := by
      change j (∫ x, k.val x • π (ofInfinite F G x) u ∂dm) = _
      rw [← hconv, haarQuotientL2IntegratedAction_apply]
      have hint : Integrable (fun x => f x • π x u) dg :=
        ((hTest k).1.1.smul hOrbc).integrable_of_hasCompactSupport (hTest k).2.1.smul_right
      change j (∫ x, f x • π x u ∂dg) =
        ∫ x, f x • haarQuotientL2BoundedRightAction F G T i hi J e hc x (j u) ∂dg
      rw [← j.integral_comp_comm hint]
      exact integral_congr_ae (ae_of_all _ fun x => by simp only [map_smul, hj])
    rw [hv]
    refine (positiveQuotientLpSmoothing_ae_eq T i hi J e hc f hfi (j u)).trans ?_
    exact ae_of_all _ fun q => by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
  have hout_add (k k' : Ck) : out (k + k') = out k + out k' := by
    funext x
    change (∫ a, liftArchimedeanKernel L (k + k').val a * base (x * a) ∂dg) = _
    simp only [liftArchimedeanKernel, Submodule.coe_add, Pi.add_apply, mul_add, add_mul]
    exact integral_add ((hdiff k).1 x) ((hdiff k').1 x)
  have hout_smul (c : ℂ) (k : Ck) : out (c • k) = c • out k := by
    funext x
    change (∫ a, liftArchimedeanKernel L (c • k).val a * base (x * a) ∂dg) = _
    rw [show (fun a => liftArchimedeanKernel L (c • k).val a * base (x * a)) =
      (fun a => c * (liftArchimedeanKernel L k.val a * base (x * a))) from funext fun a => by
        simp only [liftArchimedeanKernel, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring]
    rw [integral_const_mul]
    rfl
  let k0 : Ck := ⟨h, hhd, hhk⟩
  let Dv := SmoothVectorEnveloping.envelopingAction R hcalc
  let Ds := plotSmoothEnvelopingAction F G hsmooth hcalc
  let slice (k : Ck) (b : B) : InfinitePlotSmoothFunctions F G :=
    ⟨functionInfiniteSlice F G (out k) b, (hout k).2.1 b⟩
  have hslice_add (k k' : Ck) (b : B) : slice (k + k') b = slice k b + slice k' b :=
    Subtype.ext (congrArg (fun Φ => functionInfiniteSlice F G Φ b) (hout_add k k'))
  have hslice_smul (c : ℂ) (k : Ck) (b : B) : slice (c • k) b = c • slice k b :=
    Subtype.ext (congrArg (fun Φ => functionInfiniteSlice F G Φ b) (hout_smul c k))
  have hD (D : AdelicEnvelopingAlgebra F G hsmooth) :
      ∃ k : Ck, Dv D (vector k0) = vector k ∧ ∀ b : B, Ds D (slice k0 b) = slice k b := by
    induction D using complexEnveloping_induction with
    | h1 => exact ⟨k0, by simp, fun b => by simp⟩
    | hadd D D' ih ih' =>
      obtain ⟨k, hk, hs⟩ := ih
      obtain ⟨k', hk', hs'⟩ := ih'
      exact ⟨k + k', by simp only [map_add, LinearMap.add_apply, hk, hk', hVector_add],
        fun b => by simp only [map_add, LinearMap.add_apply, hs, hs', hslice_add]⟩
    | hsmul c D ih =>
      obtain ⟨k, hk, hs⟩ := ih
      exact ⟨c • k, by simp only [map_smul, LinearMap.smul_apply, hk, hVector_smul],
        fun b => by simp only [map_smul, LinearMap.smul_apply, hs, hslice_smul]⟩
    | hgen X D ih =>
      obtain ⟨k, hk, hs⟩ := ih
      let Y : smoothModel F d := X
      let k' : Ck := ⟨gardingKernelDerivative Y k.val, contMDiff_gardingKernelDerivative Y k.property.1,
        k.property.2.of_isClosed_subset (isClosed_tsupport _) (tsupport_gardingKernelDerivative_subset Y _)⟩
      refine ⟨k', ?_, fun b => ?_⟩
      · apply Subtype.ext
        simp only [map_mul, Module.End.mul_apply, hk, Dv, SmoothVectorEnveloping.envelopingAction_ι_tmul, one_smul]
        exact lieDerivative_gardingIntegral dm R hR _ k.property.1 k.property.2 u Y
      · apply Subtype.ext
        simp only [map_mul, Module.End.mul_apply, hs, Ds, plotSmoothEnvelopingAction_real_generator]
        funext a
        change groupDirectionalValue I X (fun y => out k (pair F G y b)) a = out k' (pair F G a b)
        rw [show out k = rightConvolution F G (liftArchimedeanKernel L k.val) base from rfl,
          (hdiff k).2.2 Y a b, liftArchimedeanKernel_derivative hsmooth L k.val Y k.property.1]
        rfl
  refine ⟨(vector k0).property, fun D => ?_⟩
  obtain ⟨k, hk, hsk⟩ := hD D
  refine ⟨out k, (hout k).1, fun g hg => positiveQuotientLpSmoothing_invariant T i _ _ ⟨g, hg⟩,
    ?_, fun b => congrArg Subtype.val (hsk b)⟩
  change (j (Dv D (vector k0)) : Q → ℂ) =ᵐ[dq] _
  rw [hk]
  exact hae k

end Langlands.Global
