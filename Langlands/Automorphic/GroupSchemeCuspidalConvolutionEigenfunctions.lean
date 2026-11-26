import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Automorphic.GroupSchemeQuotientL2IntegratedRepresentative
import Langlands.Global.AdelicNormOneClassicalCuspidalDensityStatement
import Langlands.Global.AdelicLocalFinitenessCenterStability
import Langlands.Global.AdelicRightConvolutionEnveloping
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Classical representatives in nonzero cuspidal convolution eigenspaces -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Set Filter
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus RepresentationGrowth InfiniteAdelicGroupPoints
  Langlands.GroupScheme Langlands.FiniteVectors Module.End

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (rho : MatrixRepresentation G (Fin N)) (K : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "q" => LeftCosetSpace.mk Γ
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)
local notation "V" => Lp ℂ 2 dq
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "act" => fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc dg
local notation "π" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
local notation "sm" => positiveQuotientLpSmoothing T i
local notation "W" => FinitePlotSmoothRationalFunctions F G
local notation "hcalc" => adelicDifferentialCommutator_of_smooth F G hsmooth

private local instance : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ

/-- A nonzero eigenvector of a compact smooth cuspidal convolution commuting
with a subgroup at infinity has a classical representative of uniform growth,
provided archimedean conjugation fixes the enveloping center. -/
def GroupSchemeCuspidalConvolutionEigenfunctionsStatement : Prop :=
  AdelicEnvelopingCenterConjugationStatement.{u} → 0 < N → IsClosedSubgroup rho →
  ∀ (h : A → ℂ) (_hh : IsAdelicTestFunction F G h) (hhI : Integrable h dg),
    IsCompactOperator (act h hhI) →
    (∀ k : K, ∀ v : S, π (ofInfinite F G k) (act h hhI v) = act h hhI (π (ofInfinite F G k) v)) →
    ∀ (c : ℂ), c ≠ 0 → ∀ (v : S), act h hhI v = c • v →
      ∃ φ : C(Q, ℂ), (v.val : Q → ℂ) =ᵐ[dq] φ ∧
        IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K rho (φ ∘ q) ∧
        HasZeroProperParabolicConstantTerms (φ ∘ q) ∧
        HasUniformDirectionalHeightGrowth hsmooth rho (φ ∘ q)

theorem groupSchemeCuspidalConvolutionEigenfunctions :
    GroupSchemeCuspidalConvolutionEigenfunctionsStatement T i hi I e hc hPD hG hsmooth rho K := by
  intro hAd hN hrho h hh hhI hComp hComm c hc₀ v hv
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  let : (dq).IsOpenPosMeasure := (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc).isOpenPosMeasure
  let B := act h hhI
  let E := eigenspace B.toLinearMap c
  let : FiniteDimensional ℂ E := ContinuousLinearMap.finite_dimensional_eigenspace hComp c hc₀
  have hEig (w : E) : B w.val = c • w.val := mem_eigenspace_iff.mp w.property
  obtain ⟨m, hGrowth⟩ := positiveQuotientLpSmoothing_globalGrowth T i hi I e hc hG hsmooth rho hN hrho
  let φ (k : A → ℂ) (hk : IsAdelicTestFunction F G k) (w : S) : C(Q, ℂ) :=
    ⟨LeftCosetSpace.lift Γ (sm k w.val) (positiveQuotientLpSmoothing_invariant T i k w.val),
      LeftCosetSpace.continuous_lift Γ _ _ ((hGrowth k hk).1 w.val).1⟩
  have hφ (k : A → ℂ) (hk : IsAdelicTestFunction F G k) (w : S) (x : A) :
      φ k hk w (q x) = sm k w.val x := rfl
  have hφAE (k : A → ℂ) (hk : IsAdelicTestFunction F G k) (hkI : Integrable k dg) (w : S) :
      ((act k hkI w).val : Q → ℂ) =ᵐ[dq] φ k hk w := by
    rw [fullAEL2CuspidalIntegratedAction_val]
    exact positiveQuotientLpSmoothing_ae_eq T i hi I e hc k hkI w.val
  have hφUnique (a b : C(Q, ℂ)) (he : (a : Q → ℂ) =ᵐ[dq] b) : a = b :=
    ContinuousMap.ext fun _ => congrFun (Measure.eq_of_ae_eq he a.continuous b.continuous) _
  let L : S →ₗ[ℂ] C(Q, ℂ) :=
    { toFun := φ h hh
      map_add' := by
        intro w z
        apply hφUnique
        have he := hφAE h hh hhI (w + z)
        rw [map_add] at he
        change (((B w).val + (B z).val : V) : Q → ℂ) =ᵐ[dq] φ h hh (w + z) at he
        exact he.symm.trans ((Lp.coeFn_add _ _).trans ((hφAE h hh hhI w).add (hφAE h hh hhI z)))
      map_smul' := by
        intro a w
        apply hφUnique
        have he := hφAE h hh hhI (a • w)
        rw [map_smul] at he
        change ((a • (B w).val : V) : Q → ℂ) =ᵐ[dq] φ h hh (a • w) at he
        exact he.symm.trans ((Lp.coeFn_smul a _).trans ((hφAE h hh hhI w).const_smul a)) }
  let pull : C(Q, ℂ) →ₗ[ℂ] (A → ℂ) :=
    ⟨⟨fun p => p ∘ q, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hConvolution (k : A → ℂ) (hk : IsAdelicTestFunction F G k) (hkI : Integrable k dg)
      (w : S) (p : C(Q, ℂ)) (hp : (w.val : Q → ℂ) =ᵐ[dq] p) (x : A) :
      rightConvolution F G k (p ∘ q) x = φ k hk w (q x) := by
    let a : C(A, A) := ContinuousMap.id A
    let l : C(A, ℂ) := ⟨k, hk.1.1⟩
    let p' := weightedQuotientOrbitIntegral F G T i dg a l hk.2.1 p
    have he := (groupSchemeQuotientL2IntegratedRepresentative F G T i hi I e hc dg
      a l hk.2.1 w.val p hp).2
    change (haarQuotientL2IntegratedAction F G T i hi I e hc dg k hkI w.val : Q → ℂ) =ᵐ[dq] p' at he
    rw [← fullAEL2CuspidalIntegratedAction_val] at he
    exact congrArg (fun y : C(Q, ℂ) => y (q x)) (hφUnique _ _ (he.symm.trans (hφAE k hk hkI w)))
  have hRational (k : A → ℂ) (w : S) : IsLeftInvariantUnder F G (rationalSubgroup F G) (sm k w.val) :=
    fun a ha x => positiveQuotientLpSmoothing_invariant T i k w.val
      ⟨a, rationalSubgroup_le_positiveRationalSubgroup F G T i ha⟩ x
  let Fh (w : S) : W := ofRationalSmoothFunction F G (sm h w.val) (hRational h w) ((hGrowth h hh).1 w.val)
  let M : E →ₗ[ℂ] W :=
    { toFun := fun w => Fh w.val
      map_add' := by
        intro w z
        apply finitePlotSmoothEvaluation_injective F G
        exact congrArg pull (L.map_add w.val z.val)
      map_smul' := by
        intro a w
        apply finitePlotSmoothEvaluation_injective F G
        exact congrArg pull (L.map_smul a w.val) }
  let : Module.Finite ℂ ↥(LinearMap.range M) :=
    Module.Finite.of_surjective (M.rangeRestrict) M.surjective_rangeRestrict
  let : IsNoetherian ℂ ↥(LinearMap.range M) := isNoetherian_of_isNoetherianRing_of_finite ℂ _
  have hRange (w : S) (p : C(Q, ℂ)) (hp : (w.val : Q → ℂ) =ᵐ[dq] p)
      (hEq : ∀ x : A, rightConvolution F G h (p ∘ q) x = c * p (q x)) :
      ∃ y : E, evaluate F G (M y).val = p ∘ q := by
    have hLw : L w = c • p := by
      ext z
      obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ z
      exact (hConvolution h hh hhI w p hp x).symm.trans (hEq x)
    have hwEig : B w = c • w := by
      apply Subtype.ext
      apply Lp.ext
      exact (hφAE h hh hhI w).trans (by
        change (L w : Q → ℂ) =ᵐ[dq] ((c • w).val : Q → ℂ)
        rw [hLw]
        exact (hp.const_smul c).symm.trans (Lp.coeFn_smul c w.val).symm)
    let w' : E := ⟨w, mem_eigenspace_iff.mpr hwEig⟩
    refine ⟨c⁻¹ • w', ?_⟩
    change pull (L (c⁻¹ • w)) = pull p
    rw [map_smul, hLw, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
  have hCompactStable (w : E) (k : K) :
      finitePlotSmoothInfiniteSubgroupAction F G K k (M w) ∈ LinearMap.range M := by
    let a := ofInfinite F G k
    let w' := π a w.val
    have he : B w' = c • w' := by
      rw [← hComm k w.val]
      change π a (B w.val) = _
      rw [hEig w, map_smul]
    refine ⟨⟨w', mem_eigenspace_iff.mpr he⟩, ?_⟩
    apply finitePlotSmoothEvaluation_injective F G
    let tr : C(Q, Q) := ⟨LeftCosetSpace.rightTranslate Γ a, LeftCosetSpace.continuous_rightTranslate Γ a⟩
    have ha := haarQuotientMeasureRightInvariant F G T i hi I e hc a
    have hE : (L w' : C(Q, ℂ)) = (L w.val).comp tr := by
      apply hφUnique
      refine (hφAE h hh hhI w').symm.trans ?_
      rw [show B w' = π a (B w.val) from (hComm k w.val).symm]
      exact (coeFn_quotientL2RightTranslate F G T i dq
        (haarQuotientMeasureRightInvariant F G T i hi I e hc) a (B w.val).val).trans
          (ha.quasiMeasurePreserving.ae_eq_comp (hφAE h hh hhI w.val))
    ext x
    change L w' (q x) = L w.val (q (x * a))
    rw [hE]
    rfl
  have hCenterStable (w : E) (Y : AdelicEnvelopingCenter F G hsmooth) :
      adelicCenterAction F G hsmooth hcalc Y (M w) ∈ LinearMap.range M := by
    let D := actualAdelicEnvelopingAction F G hsmooth
    have hEigen : ∀ x : A, rightConvolution F G h (evaluate F G (M w).val) x =
        c * evaluate F G (M w).val x := by
      intro x
      change rightConvolution F G h ((L w.val) ∘ q) x = c * L w.val (q x)
      have he := hConvolution h hh hhI (B w.val) (L w.val) (hφAE h hh hhI w.val) x
      change _ = L (B w.val) (q x) at he
      rw [hEig w, map_smul] at he
      exact he
    have hDEigen : ∀ x : A, rightConvolution F G h (evaluate F G (D Y.val (M w)).val) x =
        c * evaluate F G (D Y.val (M w)).val x := by
      intro x
      simpa only [Fintype.sum_unique, one_mul] using
        rightConvolution_actualAdelicEnvelopingAction_of_conjugation F G hsmooth
          (fun _ : Unit => 1) (fun _ => h) (fun _ => hh.1.1) (fun _ => hh.2.1) c (M w)
          (fun x => by simpa only [Fintype.sum_unique, one_mul] using hEigen x)
          Y.val (fun a => hAd F G hsmooth hG a Y.val Y.property) x
    obtain ⟨k, hk, _, hTransfer⟩ := adelicRightConvolutionEnveloping hsmooth hcalc Y.val h hh
    have hMeas : Measurable ((w.val.val : Q → ℂ) ∘ q) := (Lp.stronglyMeasurable w.val.val).measurable.comp
      (LeftCosetSpace.continuous_mk Γ).measurable
    have hLoc := locallyIntegrable_positiveQuotientLpPullback T i hi I e hc w.val.val
    have hDRep : evaluate F G (D Y.val (M w)).val = φ k hk w.val ∘ q := by
      funext x
      let a := infinite F G x
      let b := finite F G x
      have hs : finitePlotSmoothSlice F G b (M w) = rightConvolutionSmoothSlice hsmooth h _ hh hMeas hLoc b := rfl
      have he := finitePlotSmoothSlice_actualEnvelopingAction F G hsmooth Y.val b (M w)
      rw [hs] at he
      change _ = plotSmoothEnvelopingAction F G hsmooth hcalc Y.val _ at he
      rw [hTransfer _ hMeas hLoc b] at he
      have he' := congrArg (fun f : InfinitePlotSmoothFunctions F G => f.val a) he
      change evaluate F G (D Y.val (M w)).val (pair F G a b) = sm k w.val.val (pair F G a b) at he'
      rw [Function.comp_apply, hφ k hk w.val x]
      simpa only [a, b, pair_projections] using he'
    let hkI : Integrable k dg := hk.1.1.integrable_of_hasCompactSupport hk.2.1
    have hp : ∀ x : A, rightConvolution F G h (φ k hk w.val ∘ q) x = c * φ k hk w.val (q x) := by
      intro x
      change rightConvolution F G h (φ k hk w.val ∘ q) x = c * (φ k hk w.val ∘ q) x
      rw [← hDRep]
      exact hDEigen x
    obtain ⟨y, hy⟩ := hRange (act k hkI w.val) (φ k hk w.val) (hφAE k hk hkI w.val) hp
    refine ⟨y, finitePlotSmoothEvaluation_injective F G ?_⟩
    exact hy.trans hDRep.symm
  let v' : E := c⁻¹ • (⟨v, mem_eigenspace_iff.mpr hv⟩ : E)
  have hv' : B v'.val = v := by
    change B (c⁻¹ • v) = v
    rw [map_smul, hv, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
  let p := L v'.val
  have hpAE : (v.val : Q → ℂ) =ᵐ[dq] p := by
    rw [← hv']
    exact hφAE h hh hhI v'.val
  have hR : evaluate F G (M v').val = p ∘ q := rfl
  have hCF : IsAdelicInfiniteFinite F G K (M v') := by
    have hLe : orbitSpan (finitePlotSmoothInfiniteSubgroupAction F G K) (M v') ≤ LinearMap.range M :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hCompactStable _ k)
    exact Module.Finite.of_injective (Submodule.inclusion hLe) (Submodule.inclusion_injective hLe)
  have hZF : IsAdelicCenterFinite F G hsmooth hcalc (M v') := by
    have hLe : orbitSpan (adelicCenterAction F G hsmooth hcalc).toMonoidHom (M v') ≤ LinearMap.range M :=
      Submodule.span_le.mpr (by rintro _ ⟨Y, rfl⟩; exact hCenterStable _ Y)
    exact Module.Finite.of_injective (Submodule.inclusion hLe) (Submodule.inclusion_injective hLe)
  have hpGrow : HasUniformDirectionalHeightGrowth hsmooth rho (p ∘ q) := by
    refine ⟨m, Nat.cast_nonneg _, fun s => ?_⟩
    obtain ⟨C, hC, hBound⟩ := (hGrowth h hh).2 s
    refine ⟨C * ‖v'.val.val‖, mul_nonneg hC (norm_nonneg _), fun x => ?_⟩
    change ‖adelicIteratedDirectionalValue hsmooth s (sm h v'.val.val) x‖ ≤ _
    rw [Real.rpow_natCast, mul_right_comm C]
    exact hBound v'.val.val x
  have hMod : HasModerateGrowthFunction F G rho (p ∘ q) := by
    obtain ⟨b, hb, hD⟩ := hpGrow
    obtain ⟨C, hC, hDer⟩ := hD []
    exact (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
      ⟨C, b, hC, hb, by simpa only [adelicIteratedDirectionalValue_nil] using hDer⟩
  refine ⟨p, hpAE, ?_, ?_, hpGrow⟩
  · rw [← hR, isAutomorphicFunctionOn_evaluate_iff]
    refine ⟨hCF, hZF, ?_⟩
    change HasModerateGrowthFunction F G rho (evaluate F G (M v').val)
    rw [hR]
    exact hMod
  · exact hasZeroProperParabolicConstantTerms_of_normalized hPD hG _
      ((groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc p v.val hpAE).mp v.property)

end Langlands.Automorphic.GroupSchemeFunctions
