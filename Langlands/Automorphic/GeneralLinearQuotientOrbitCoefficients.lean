import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction
import Langlands.Automorphic.GroupSchemeQuotientL2IntegratedRepresentative
import Langlands.Automorphic.CuspidalAdmissible.Reproduction
import Langlands.Global.ArchimedeanConvolutionDifferentiationProof

/-! # Scalar orbit coefficients of represented stable forms on the positive quotient -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

set_option maxHeartbeats 900000 in
/-- The differentiated reproduction identity at an arbitrary archimedean translate. -/
private theorem OperatorRealization.enveloping_eval_at_translate_of_reproducesAt
    {F : Type u} [Field F] [NumberField F] {n : ℕ}
    [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
    (ν : Measure (InfiniteAdelicGL F n)) [IsFiniteMeasureOnCompacts ν]
    (R : OperatorRealization F n) (f : R.Space) (x : AdelicGL F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n)
    (hx : R.ReproducesAt ν κ.val.val f x) (D : ArchimedeanGL.EnvelopingAlgebra F n)
    (g : InfiniteAdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n (R.toContinuous (R.envelopingAction D f)) (x * AdelicGL.ofInfinite F n g) =
      ∫ z, ContinuousRationalFunctions.evaluate F n (R.toContinuous f) (x * AdelicGL.ofInfinite F n z) *
        (ArchimedeanGL.envelopingAction F n D κ.val).val (z⁻¹ * g) ∂ν := by
  let a := AdelicGL.infinite F n x
  let b := AdelicGL.finite F n x
  let s := finiteSmoothSlice F n b (R.ambient f)
  let t := ArchimedeanGL.smoothLeftTranslation F n a s
  have hxs : AdelicGL.pair F n a b = x := AdelicGL.pair_projections F n x
  have hpair (z : InfiniteAdelicGL F n) :
      x * AdelicGL.ofInfinite F n z = AdelicGL.pair F n (a * z) b := by
    rw [AdelicGL.ofInfinite_eq_pair, ← hxs, AdelicGL.pair_mul, mul_one]
  have ht (z : InfiniteAdelicGL F n) :
      t.val z = ContinuousRationalFunctions.evaluate F n (R.toContinuous f) (x * AdelicGL.ofInfinite F n z) := by
    change (ArchimedeanGL.smoothLeftTranslation F n a s).val z = _
    rw [ArchimedeanGL.smoothLeftTranslation_apply, hpair, R.evaluate_toContinuous]
    exact finiteSmoothSlice_apply F n b (R.ambient f) (a * z)
  have htc (z : InfiniteAdelicGL F n) : ArchimedeanGL.toContinuousMap F n t z =
      ContinuousRationalFunctions.evaluate F n (R.toContinuous f) (x * AdelicGL.ofInfinite F n z) := ht z
  obtain ⟨j, hj, hD⟩ := ArchimedeanGL.compactKernelConvolutionDifferentiation F n ν
    (ArchimedeanGL.toContinuousMap F n t) κ
  have hjt : j = t := by
    apply Subtype.ext
    funext z
    rw [hj, ArchimedeanGL.rawConvolution_apply, ht z, hx z]
    simp only [htc]
  calc
    _ = (ArchimedeanGL.envelopingAction F n D s).val (a * g) := by
      rw [R.evaluate_toContinuous, R.ambient_envelopingAction, hpair]
      exact evaluate_finiteSmoothEnvelopingAction F n D (R.ambient f) (a * g) b
    _ = (ArchimedeanGL.envelopingAction F n D t).val g := by
      change _ = (ArchimedeanGL.envelopingAction F n D
        (ArchimedeanGL.smoothLeftTranslation F n a s)).val g
      rw [ArchimedeanGL.envelopingAction_leftTranslation_eval]
    _ = _ := by
      rw [← hjt]
      simpa only [htc] using hD D g

namespace GroupSchemeFunctions

open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

section Coefficients

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "n" => r + 1
local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "Γ" => positiveRationalSubgroup F GLs T i
local notation "Q" => PositiveRationalQuotient F GLs T i
local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
local notation "E" => Lp ℂ 2 μQ
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F n
local notation "b∞" => fun g => ContinuousMulEquiv.symm m (AdelicGL.ofInfinite F n g)

set_option maxHeartbeats 1600000 in
private theorem weightedClass_eq_of_pointwise
    {Y : Type v} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (b : C(Y, AdelicGroupPoints F GLs)) (w : C(Y, ℂ)) (hw : HasCompactSupport w)
    (φ ψ : E) (f g : Langlands.Automorphic.ContinuousRationalFunctions F n)
    (hf : IsGeneralLinearFormClass F r T i φ f) (hg : IsGeneralLinearFormClass F r T i ψ g)
    (hpoint : ∀ x : AdelicGL F n, ContinuousRationalFunctions.evaluate F n g x =
      ∫ z, w z * ContinuousRationalFunctions.evaluate F n f (x * m (b z)) ∂ν) :
    Integrable (fun z => w z • ρ (b z) φ) ν ∧ (∫ z, w z • ρ (b z) φ ∂ν) = ψ := by
  obtain ⟨h, hPull, hRep⟩ := hf
  obtain ⟨hI, hAE⟩ := groupSchemeQuotientL2IntegratedRepresentative F GLs T i hi I e hc
    (Y := Y) ν b w hw φ h hRep
  refine ⟨hI, IsGeneralLinearFormClass.unique ?_ hg⟩
  let k := weightedQuotientOrbitIntegral F GLs T i ν b w hw h
  refine ⟨k, ?_, hAE⟩
  have hEval (l : C(Q, ℂ)) (x : AdelicGL F n) :
      ContinuousRationalFunctions.evaluate F n
        (continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLs T i l)) x =
          l (LeftCosetSpace.mk Γ ((m).symm x)) := by
    rw [evaluate_continuousGeneralLinearEquiv]
    rfl
  have hfEval (x : AdelicGL F n) :
      h (LeftCosetSpace.mk Γ ((m).symm x)) = ContinuousRationalFunctions.evaluate F n f x := by
    rw [← hEval h x, hPull]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ContinuousRationalFunctions.evaluate F n
    (continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLs T i k)) x =
      ContinuousRationalFunctions.evaluate F n g x
  rw [hEval k x, hpoint x]
  unfold k
  rw [weightedQuotientOrbitIntegral_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    have hMul : (m).symm (x * m (b z)) = (m).symm x * b z := by
      rw [map_mul, (m).symm_apply_apply]
    change w z * h (LeftCosetSpace.rightTranslate Γ (b z) (LeftCosetSpace.mk Γ ((m).symm x))) =
      w z * ContinuousRationalFunctions.evaluate F n f (x * m (b z))
    rw [LeftCosetSpace.rightTranslate_mk, ← hMul, hfEval]

/-- Scalar orbit coefficients of stable forms with classes on the original quotient are
smooth at infinity. Their enveloping derivatives are the corresponding coefficients of the
pointwise enveloping derivatives of those forms. -/
def GeneralLinearQuotientOrbitCoefficientsStatement : Prop :=
  ∀ [CompactSpace (AdeleQuotient F)] (R : OperatorRealization F n)
    (j : R.Space →ₗ[ℂ] E), (∀ f, IsGeneralLinearFormClass F r T i (j f) (R.toContinuous f)) →
    ∀ ℓ : E →L[ℂ] ℂ, ∃ C : R.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n,
      (∀ f g, (C f).val g = ℓ (ρ (b∞ g) (j f))) ∧
      ∀ D f, ArchimedeanGL.envelopingAction F n D (C f) = C (R.envelopingAction D f)

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Transfer derivatives to a compact reproducing kernel and commute the scalar functional
with the Bochner integral of the original quotient classes. -/
theorem generalLinearQuotientOrbitCoefficients :
    GeneralLinearQuotientOrbitCoefficientsStatement F r T i hi I e hc := by
  classical
  intro _ R j hj ℓ
  let : SecondCountableTopology (InfiniteAdelicGL F n) :=
    (GeneralLinearGroupPoints.infiniteHomeomorph F n).symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : MeasurableSpace (InfiniteAdelicGL F n) := ArchimedeanGL.borelMeasurableSpace F n
  let : BorelSpace (InfiniteAdelicGL F n) := ArchimedeanGL.borelMeasurableSpace_borelSpace F n
  let ν := ArchimedeanGL.leftHaarMeasure F n
  let : ν.IsHaarMeasure := ArchimedeanGL.leftHaarMeasure_isHaarMeasure F n
  let b : C(InfiniteAdelicGL F n, AdelicGroupPoints F GLs) :=
    ⟨b∞, (m).symm.continuous.comp (AdelicGL.ofInfinite F n).continuous⟩
  let cf (f : R.Space) : C(InfiniteAdelicGL F n, ℂ) :=
    ⟨fun g => ℓ (ρ (b g) (j f)), ℓ.continuous.comp
      ((haarQuotientL2OrbitMap F GLs T i hi I e hc (j f)).continuous.comp b.continuous)⟩
  have hex (f : R.Space) : ∃ s : ArchimedeanGL.SmoothFunctions F n,
      (∀ g, s.val g = cf f g) ∧
      ∀ D g, (ArchimedeanGL.envelopingAction F n D s).val g = cf (R.envelopingAction D f) g := by
    obtain ⟨κ, hκ⟩ := R.exists_reproducingKernel ν f
    obtain ⟨s, _, hD⟩ := ArchimedeanGL.compactKernelConvolutionDifferentiation F n ν (cf f) κ
    have hdiff (D : ArchimedeanGL.EnvelopingAlgebra F n) (g : InfiniteAdelicGL F n) :
        (ArchimedeanGL.envelopingAction F n D s).val g = cf (R.envelopingAction D f) g := by
      let κ' := ArchimedeanGL.envelopingAction F n D κ.val
      let τ := (Homeomorph.inv (InfiniteAdelicGL F n)).trans (Homeomorph.mulRight g)
      let w : C(InfiniteAdelicGL F n, ℂ) := ⟨fun z => κ'.val (z⁻¹ * g),
        (ArchimedeanGL.continuous F n κ').comp τ.continuous⟩
      have hw : HasCompactSupport w :=
        (ArchimedeanGL.envelopingCompactSupport F n D κ.val κ.property).comp_homeomorph τ
      have hT := (hj (R.envelopingAction D f)).rightTranslate
        (haarQuotientMeasureRightInvariant F GLs T i hi I e hc) (b g)
      have hmg (z : InfiniteAdelicGL F n) : m (b z) = AdelicGL.ofInfinite F n z :=
        (m).apply_symm_apply _
      obtain ⟨hI, heq⟩ := weightedClass_eq_of_pointwise F r T i hi I e hc
        (Y := InfiniteAdelicGL F n) ν b w hw _ _ _ _ (hj f) hT (fun x => by
          change ContinuousRationalFunctions.evaluate F n (R.toContinuous (R.envelopingAction D f))
            (x * m (b g)) = _
          simp only [hmg]
          exact (R.enveloping_eval_at_translate_of_reproducesAt ν f x κ (hκ x) D g).trans
            (integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ (w z))))
      change (∫ z, w z • ρ (b z) (j f) ∂ν) = ρ (b g) (j (R.envelopingAction D f)) at heq
      change (ArchimedeanGL.envelopingAction F n D s).val g = ℓ (ρ (b g) (j (R.envelopingAction D f)))
      rw [← heq, ← ℓ.integral_comp_comm hI, hD D g]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change cf f z * w z = ℓ (w z • ρ (b z) (j f))
        rw [map_smul, smul_eq_mul]
        exact mul_comm _ _
    exact ⟨s, fun g => by simpa only [map_one, Module.End.one_apply] using hdiff 1 g, hdiff⟩
  choose v hv hD using hex
  let C : R.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n := {
    toFun := v
    map_add' f f' := by
      apply Subtype.ext
      funext g
      change (v (f + f')).val g = (v f).val g + (v f').val g
      rw [hv, hv, hv]
      change ℓ (ρ (b g) (j (f + f'))) = ℓ (ρ (b g) (j f)) + ℓ (ρ (b g) (j f'))
      simp only [map_add]
    map_smul' c f := by
      apply Subtype.ext
      funext g
      change (v (c • f)).val g = c • (v f).val g
      rw [hv, hv]
      change ℓ (ρ (b g) (j (c • f))) = c • ℓ (ρ (b g) (j f))
      simp only [map_smul] }
  refine ⟨C, hv, fun D f => ?_⟩
  apply Subtype.ext
  funext g
  exact (hD f D g).trans (hv (R.envelopingAction D f) g).symm

end Coefficients
end GroupSchemeFunctions
end Langlands.Automorphic
