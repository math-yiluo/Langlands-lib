import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Automorphic.CuspidalUnitaryForm
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiation of actual global Whittaker integrals along Lie curves -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology Metric
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace WhittakerCurve

section CompactQuotient

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H)

/-- Invariant functions evaluated at quotient representatives vary continuously whenever
their pullback to the group does. This does not require a continuous choice of representatives. -/
theorem continuous_out_family {E : Type*} [TopologicalSpace E] {Φ : E → H → ℂ}
    (hΦ : ∀ e (k : Γ) x, Φ e ((k : H) * x) = Φ e x)
    (hc : Continuous (Function.uncurry Φ)) :
    Continuous (fun p : E × LeftCosetSpace Γ => Φ p.1 p.2.out) := by
  have hq : IsOpenQuotientMap
      (Prod.map (id : E → E) (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  apply hq.isQuotientMap.continuous_iff.mpr
  convert hc using 1
  funext p
  exact congrFun (Unfolding.out_eq_lift Γ (Φ p.1) (hΦ p.1))
    (LeftCosetSpace.mk Γ p.2)

variable [CompactSpace (LeftCosetSpace Γ)]
    [MeasurableSpace (LeftCosetSpace Γ)] [BorelSpace (LeftCosetSpace Γ)]
    (nu : Measure (LeftCosetSpace Γ)) [IsFiniteMeasure nu]

/-- Dominated differentiation on a compact left quotient, with the local uniform derivative
bound derived from joint continuity and compactness. -/
theorem hasDerivAt_integral_out {Φ Ψ : ℝ → H → ℂ}
    (hΦ : ∀ s (k : Γ) x, Φ s ((k : H) * x) = Φ s x)
    (hΦc : ∀ s, Continuous (Φ s))
    (hΨ : ∀ s (k : Γ) x, Ψ s ((k : H) * x) = Ψ s x)
    (hΨc : Continuous (Function.uncurry Ψ))
    (hd : ∀ y t, HasDerivAt (fun s => Φ s y) (Ψ t y) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ q, Φ s q.out ∂nu) (∫ q, Ψ t q.out ∂nu) t := by
  have hcΨ := continuous_out_family Γ hΨ hΨc
  have hcΦ : ∀ s, Continuous (fun q : LeftCosetSpace Γ => Φ s q.out) := by
    intro s
    rw [Unfolding.out_eq_lift Γ (Φ s) (hΦ s)]
    exact LeftCosetSpace.continuous_lift Γ _ _ (hΦc s)
  obtain ⟨C, hC⟩ := (isCompact_closedBall t 1 |>.prod
    (isCompact_univ : IsCompact (Set.univ : Set (LeftCosetSpace Γ)))).exists_bound_of_continuousOn
      hcΨ.continuousOn
  have hcΨt : ∀ s, Continuous (fun q : LeftCosetSpace Γ => Ψ s q.out) :=
    fun s => hcΨ.comp (Continuous.prodMk_right s)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℂ)
    (μ := nu) (F := fun s q => Φ s q.out) (F' := fun s q => Ψ s q.out)
    (x₀ := t) (bound := fun _ => C) (closedBall_mem_nhds t one_pos)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hcΦ s).aestronglyMeasurable
  · exact (hcΦ t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hcΨt t).aestronglyMeasurable
  · exact ae_of_all _ fun q s hs => hC (s, q) ⟨hs, Set.mem_univ _⟩
  · exact integrable_const C
  · exact ae_of_all _ fun q s _ => hd q.out s

end CompactQuotient

section Actual

open scoped CategoryTheory.MonObj
open Langlands.Automorphic
open Langlands.Global.ArchimedeanGL

local instance curveSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance curveSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance curveRationalAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance curveContinuousAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance curveSmoothAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance curveFormsAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance curveStableAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance curveSpaceAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The genuine adelic right-translation curve of a real archimedean Lie direction. -/
def adelicOneParameter (n : ℕ) (X : RealLieAlgebra F n) (s : ℝ) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (AdelicGL.ofInfinite F n (infiniteOneParameter F n X s))

omit [CompactSpace (AdeleQuotient F)] in
theorem continuous_adelicOneParameter (n : ℕ) (X : RealLieAlgebra F n) :
    Continuous (adelicOneParameter F n X) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    ((map_continuous (AdelicGL.ofInfinite F n)).comp (continuous_infiniteOneParameter F n X))

/-- Actual realized forms differentiate along the genuine adelic one-parameter curve. -/
theorem cuspFunction_hasDerivAt {r : ℕ} (T : CuspidalOperatorRealization F r)
    (X : RealLieAlgebra F (r + 1)) (x : T.Space) (g : Points F (r + 1)) (t : ℝ) :
    HasDerivAt (fun s => cuspFunction F T x (g * adelicOneParameter F (r + 1) X s))
      (cuspFunction F T (T.realization.lieOperator X x)
        (g * adelicOneParameter F (r + 1) X t)) t := by
  simp only [RealPlaceWhittaker.cuspFunction_eq_evaluate, map_mul, adelicOneParameter,
    MulEquiv.apply_symm_apply]
  exact T.realization.hasDerivAt_evaluate_oneParameter X x
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g) t

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 300000 in
theorem cuspWhittaker_hasDerivAt {r : ℕ} (T : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (X : RealLieAlgebra F (r + 1)) (x : T.Space) (g : Points F (r + 1)) (t : ℝ) :
    HasDerivAt (fun s => cuspWhittaker F T χ x (g * adelicOneParameter F (r + 1) X s))
      (cuspWhittaker F T χ (T.realization.lieOperator X x)
        (g * adelicOneParameter F (r + 1) X t)) t := by
  let Γ := AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))
  let θ := genericCharacter F r χ (fun _ => 1)
  let e := adelicOneParameter F (r + 1) X
  let Φ : ℝ → unipotentAdelic F (r + 1) → ℂ := fun s n =>
    cuspFunction F T x (n.val * (g * e s)) * starRingEnd ℂ (θ n)
  let Ψ : ℝ → unipotentAdelic F (r + 1) → ℂ := fun s n =>
    cuspFunction F T (T.realization.lieOperator X x) (n.val * (g * e s)) *
      starRingEnd ℂ (θ n)
  have hInv (y : T.Space) (s : ℝ) (k : Γ) (n : unipotentAdelic F (r + 1)) :
      cuspFunction F T y (((k : unipotentAdelic F (r + 1)) * n).val * (g * e s)) *
          starRingEnd ℂ (θ ((k : unipotentAdelic F (r + 1)) * n)) =
        cuspFunction F T y (n.val * (g * e s)) * starRingEnd ℂ (θ n) := by
    rw [Subgroup.coe_mul, mul_assoc,
      Unfolding.cuspFunction_rational_mul F T y
        (Unfolding.mem_rationalSubgroup_of_unipotent F k)]
    exact congrArg (cuspFunction F T y (n.val * (g * e s)) * ·)
      (congrArg (starRingEnd ℂ) (Unfolding.genericCharacter_rational_mul F r χ hχ k n))
  have hCont (y : T.Space) :
      Continuous (fun p : ℝ × unipotentAdelic F (r + 1) =>
        cuspFunction F T y (p.2.val * (g * e p.1)) * starRingEnd ℂ (θ p.2)) :=
    ((Unfolding.continuous_cuspFunction F T y).comp
      ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_const.mul ((continuous_adelicOneParameter F (r + 1) X).comp continuous_fst)))).mul
      (Complex.continuous_conj.comp
        ((Unfolding.continuous_genericCharacter F r χ hχ.1 _).comp continuous_snd))
  let := Unfolding.compactSpace_unipotentRationalQuotient F (r + 1)
  let := AdelicSubgroupPoints.rationalQuotientBorelSpace F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))
  let := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure
    F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
  have hΦc : ∀ s, Continuous (Φ s) := by
    intro s
    dsimp only [Φ]
    exact ((Unfolding.continuous_cuspFunction F T x).comp
      (continuous_subtype_val.mul_const (g * e s))).mul
        (Complex.continuous_conj.comp (Unfolding.continuous_genericCharacter F r χ hχ.1 _))
  have hΨc : Continuous (Function.uncurry Ψ) := by
    change Continuous (fun p : ℝ × unipotentAdelic F (r + 1) =>
      cuspFunction F T (T.realization.lieOperator X x) (p.2.val * (g * e p.1)) *
        starRingEnd ℂ (θ p.2))
    exact hCont (T.realization.lieOperator X x)
  have hdΦ : ∀ (n : unipotentAdelic F (r + 1)) s,
      HasDerivAt (fun v => Φ v n) (Ψ s n) s := by
    intro n s
    have hd := (cuspFunction_hasDerivAt F T X x (n.val * g) s).mul_const
      (starRingEnd ℂ (θ n))
    simpa only [Φ, Ψ, e, mul_assoc] using hd
  have hdint := hasDerivAt_integral_out Γ
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
      (upperUnipotent F (r + 1))) (Φ := Φ) (Ψ := Ψ)
    (hInv x) hΦc (hInv (T.realization.lieOperator X x)) hΨc hdΦ t
  simp only [cuspWhittaker, generalLinearWhittakerFunction,
    Unfolding.subgroupCharacterCoefficient_eq_integral, Unfolding.coefficientIntegrand]
  exact hdint

end Actual
end WhittakerCurve
end Langlands.Global.RankinSelbergGlobal
