import Langlands.Global.AdelicL2FiniteVectorDensity
import Langlands.Global.AdelicQuotientConvolutionGrowth
import Langlands.Analysis.Local.QuotientConvolutionKernelProof
import Langlands.Analysis.Local.QuotientNormalizingFunction
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof
import Langlands.Global.AdelicRightConvolutionDifferentiation
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof

/-! # Smoothing of `L²([G])` classes by adelic test kernels

For the canonical quotient `[G] = A_G G(F) \ G(𝔸)` and a class `v ∈ L²([G])`,
`canonicalL2Smoothing h v` is the right convolution `x ↦ ∫ h(a) v(x a) da` of the pullback of `v`
to `G(𝔸)`. For a test kernel it is smooth, left invariant under `A_G G(F)`, of moderate growth
(Mœglin–Waldspurger I.2.4–I.2.5) and represents the integrated right action `R(h) v`. The module
also proves that continuous left `A_G G(F)`-invariant functions that agree almost everywhere on
`[G]` are equal, and that orthogonal projections onto closed invariant subspaces commute with
`R(g)` and `R(h)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise InnerProductSpace ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

namespace RestrictionSplitCentre

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.QuotientIntegration

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "μ" => canonicalMeasure F G
local notation "Γ" => canonicalRationalSubgroup F G
local notation "dg" => (Measure.haar : Measure (AdelicGroupPoints F G))

/-- The pullback to `G(𝔸)` of the chosen representative of a class of `L²([G])`. -/
def canonicalL2Pullback (v : Lp ℂ 2 μ) : AdelicGroupPoints F G → ℂ :=
  fun x => v (LeftCosetSpace.mk Γ x)

/-- The pullback of a class is measurable. -/
theorem measurable_canonicalL2Pullback (v : Lp ℂ 2 μ) : Measurable (canonicalL2Pullback v) :=
  (Lp.stronglyMeasurable v).measurable.comp (LeftCosetSpace.measurable_mk Γ)

/-- The pullback of a class is left invariant under `A_G G(F)`. -/
theorem canonicalL2Pullback_mul (v : Lp ℂ 2 μ) (c : AdelicGroupPoints F G) (hc : c ∈ Γ)
    (x : AdelicGroupPoints F G) : canonicalL2Pullback v (c * x) = canonicalL2Pullback v x := by
  unfold canonicalL2Pullback
  rw [LeftCosetSpace.mk_subgroup_mul Γ ⟨c, hc⟩ x]

/-- Right convolution `x ↦ ∫ h(a) v(x a) da` of the pullback of a class `v` of `L²([G])`. -/
def canonicalL2Smoothing (h : AdelicGroupPoints F G → ℂ) (v : Lp ℂ 2 μ) :
    AdelicGroupPoints F G → ℂ :=
  rightConvolution F G h (canonicalL2Pullback v)

/-- Smoothing is left invariant under `A_G G(F)`. -/
theorem canonicalL2Smoothing_mul (h : AdelicGroupPoints F G → ℂ) (v : Lp ℂ 2 μ)
    (c : AdelicGroupPoints F G) (hc : c ∈ Γ) (x : AdelicGroupPoints F G) :
    canonicalL2Smoothing h v (c * x) = canonicalL2Smoothing h v x := by
  unfold canonicalL2Smoothing rightConvolution
  congr 1
  funext a
  rw [mul_assoc, canonicalL2Pullback_mul v c hc]

section Reductive

variable (hG : IsConnectedReductive G)

include hG in
/-- The canonical subgroup Haar measure on `A_G G(F)` is σ-finite. -/
theorem canonicalSubgroupHaarMeasure_sigmaFinite :
    SigmaFinite (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG) := by
  have hΓ := isClosed_canonicalRationalSubgroup F G centralSplitTorusCharacter hG
  let := canonicalSubgroupHaarMeasure_isHaarMeasure F G centralSplitTorusCharacter hG
  have : LocallyCompactSpace Γ := hΓ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology Γ :=
    TopologicalSpace.Subtype.secondCountableTopology (Γ : Set (AdelicGroupPoints F G))
  have : SigmaCompactSpace Γ := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

include hG in
/-- The kernel vectors of right convolution on `L²([G])` (`quotientConvolutionKernel` for the
canonical quotient). -/
theorem exists_canonicalConvolutionKernel (f : C_c(AdelicGroupPoints F G, ℂ)) :
    ∃ v : AdelicGroupPoints F G → Lp ℂ 2 μ, Continuous v ∧
      (∀ (x : AdelicGroupPoints F G) (φ : Lp ℂ 2 μ),
        Integrable (fun a => f a * φ (LeftCosetSpace.mk Γ (x * a))) dg ∧
          inner ℂ (v x) φ = ∫ a, f a * φ (LeftCosetSpace.mk Γ (x * a)) ∂dg) ∧
      ∀ (x : AdelicGroupPoints F G) (M : ℝ), (∀ a, ‖f a‖ ≤ M) →
        ‖v x‖ ^ 2 ≤ M * (∫ a, ‖f a‖ ∂dg) *
          (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG).real
            (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' (tsupport f * (tsupport f)⁻¹))) := by
  let := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  let : IsFiniteMeasure μ := connectedReductiveQuotientFiniteVolume F G hG _ _
    (isSplitComponent_canonicalRestrictionComponent F G)
  have hΓ := isClosed_canonicalRationalSubgroup F G centralSplitTorusCharacter hG
  let := canonicalSubgroupHaarMeasure_isHaarMeasure F G centralSplitTorusCharacter hG
  let := canonicalSubgroupHaarMeasure_sigmaFinite hG
  exact quotientConvolutionKernel Γ hΓ (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG)
    dg μ (canonicalMeasure_isCompatible F G centralSplitTorusCharacter hG) f

include hG in
/-- The pullback of a class of `L²([G])` is locally integrable on `G(𝔸)`. -/
theorem locallyIntegrable_canonicalL2Pullback (v : Lp ℂ 2 μ) :
    LocallyIntegrable (canonicalL2Pullback v) dg := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  obtain ⟨b, hbS, _, hbComp, _⟩ :=
    exists_continuous_one_zero_of_isCompact hS isClosed_empty (disjoint_empty S)
  let h : C_c(AdelicGroupPoints F G, ℂ) :=
    ⟨⟨fun x => (b x : ℂ), Complex.continuous_ofReal.comp b.continuous⟩,
      hbComp.comp_left Complex.ofReal_zero⟩
  obtain ⟨_, _, hIntegrable, _⟩ := exists_canonicalConvolutionKernel hG h
  apply ((hIntegrable 1 v).1).integrableOn.congr
  filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
  have hb : b x = 1 := hbS hx
  change (b x : ℂ) * v (LeftCosetSpace.mk Γ (1 * x)) = v (LeftCosetSpace.mk Γ x)
  simp only [hb, Complex.ofReal_one, one_mul]

include hG in
/-- Smoothing by a test kernel gives a smooth function on `G(𝔸)`. -/
theorem isAdelicSmoothFunction_canonicalL2Smoothing {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : AdelicGroupPoints F G → ℂ}
    (hh : IsAdelicTestFunction F G h) (v : Lp ℂ 2 μ) :
    IsAdelicSmoothFunction F G (canonicalL2Smoothing h v) :=
  (adelicRightConvolutionDifferentiation F G d hsmooth h _ hh (measurable_canonicalL2Pullback v)
    (locallyIntegrable_canonicalL2Pullback hG v)).2.1

/-- The integrated right regular representation `R(h) = ∫ h(g) R(g) dg` on `L²([G])`. -/
def canonicalL2IntegratedAction (h : AdelicGroupPoints F G → ℂ) (hh : Integrable h dg) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  Langlands.Analysis.integratedIsometricAction dg (canonicalL2BoundedRightAction hG)
    (fun g φ => norm_canonicalL2RightAction hG g φ)
    (fun φ => (continuous_canonicalL2RightAction_orbit hG φ).aestronglyMeasurable) h hh

/-- The integrated action is the Bochner integral of the weighted orbit. -/
theorem canonicalL2IntegratedAction_apply (h : AdelicGroupPoints F G → ℂ) (hh : Integrable h dg)
    (φ : Lp ℂ 2 μ) :
    canonicalL2IntegratedAction hG h hh φ =
      ∫ g, h g • canonicalL2RightAction F G centralSplitTorusCharacter hG g φ ∂dg := rfl

/-- The integrated action is represented almost everywhere by the pointwise smoothing. -/
theorem canonicalL2IntegratedAction_ae_eq (h : AdelicGroupPoints F G → ℂ) (hh : Integrable h dg)
    (v : Lp ℂ 2 μ) :
    (canonicalL2IntegratedAction hG h hh v : CanonicalQuotient F G → ℂ) =ᵐ[μ]
      fun y => canonicalL2Smoothing h v y.out := by
  let := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  let : IsFiniteMeasure μ := connectedReductiveQuotientFiniteVolume F G hG _ _
    (isSplitComponent_canonicalRestrictionComponent F G)
  let r := canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG
  let act (x : CanonicalQuotient F G) (a : AdelicGroupPoints F G) :=
    LeftCosetSpace.rightTranslate Γ a x
  have hAct : Continuous (fun z : CanonicalQuotient F G × AdelicGroupPoints F G => act z.1 z.2) :=
    continuous_smul.comp ((MulOpposite.continuous_op.comp continuous_snd).prodMk continuous_fst)
  have hp := Langlands.Analysis.integratedTranslationPointwise (CanonicalQuotient F G) μ
    (AdelicGroupPoints F G) dg act hAct.measurable r
    (canonicalL2BoundedRightAction hG)
    (fun g φ => norm_canonicalL2RightAction hG g φ)
    (fun φ => (continuous_canonicalL2RightAction_orbit hG φ).aestronglyMeasurable)
    (fun a v => Lp.coeFn_compMeasurePreserving v (r a)) h hh v
  refine hp.2.trans (Filter.Eventually.of_forall fun y => ?_)
  change ∫ g, h g * v (LeftCosetSpace.rightTranslate Γ g y) ∂dg =
    ∫ g, h g * v (LeftCosetSpace.mk Γ (y.out * g)) ∂dg
  congr 1
  funext g
  conv_lhs => rw [← Quotient.out_eq y]
  rfl


include hG in
/-- The canonical Haar measure of `A_G G(F)` has the same mass on adelic conjugates of compact
sets as the positive-rational subgroup measure, so it inherits its polynomial bound at every
adelic point. -/
theorem canonicalSubgroupConjugateGrowth {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ d : ℕ, ∀ (S : Set (AdelicGroupPoints F G)), IsCompact S → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : AdelicGroupPoints F G,
        (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG).real
          (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) ≤
            B * RepresentationGrowth.adelicHeight F G rho x ^ d := by
  have := canonical_finiteIndex F G hG
  have hs := isSplitComponent_canonicalComponent F G
  have hi := canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
  obtain ⟨I, hI, ⟨e⟩⟩ := hs.1.1.1
  let := Fintype.ofFinite I
  obtain ⟨d, hd⟩ := PositiveRealTorus.adelicPositiveRationalConjugateGrowth_allPoints rho
    (canonicalTorus F G) (canonicalComponent F G) hi I e hs.1.2 hN hrho
  refine ⟨d, fun S hS => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hd S hS
  refine ⟨B, hB, fun x => ?_⟩
  have key : ∀ (H₁ H₂ : Subgroup (AdelicGroupPoints F G)) (hH : H₁ = H₂) (ν : Measure H₁)
      (X : Set (AdelicGroupPoints F G)),
      (ν.map (MulEquiv.subgroupCongr hH)) (Subtype.val ⁻¹' X) = ν (Subtype.val ⁻¹' X) := by
    intro H₁ H₂ hH ν X
    subst hH
    have hid : ⇑(MulEquiv.subgroupCongr (rfl : H₁ = H₁)) = id := rfl
    rw [hid, Measure.map_id]
  have heq : (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG).real
      (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) =
      (PositiveRealTorus.positiveRationalSubgroupHaarMeasure F G (canonicalTorus F G)
        (canonicalComponent F G) hi I e hs.1.2).real
          (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) := by
    unfold canonicalSubgroupHaarMeasure subgroupHaarMeasure
    rw [PositiveRealTorus.intrinsicPositiveRationalSubgroupHaarMeasure_eq F G _ _ hi I e hs.1.2
      hs.1.1.1, measureReal_def, measureReal_def, key]
  rw [heq]
  exact hbound x

include hG in
/-- Smoothing by a continuous compactly supported kernel is bounded by a power of the adelic
height times the norm of the class, at every adelic point. -/
theorem exists_canonicalL2Smoothing_bound {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) (f : C_c(AdelicGroupPoints F G, ℂ)) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Lp ℂ 2 μ) (x : AdelicGroupPoints F G),
      ‖canonicalL2Smoothing (f : AdelicGroupPoints F G → ℂ) v x‖ ≤
        C * RepresentationGrowth.adelicHeight F G rho x ^ m * ‖v‖ := by
  obtain ⟨m, hMass⟩ := canonicalSubgroupConjugateGrowth hG rho hN hrho
  obtain ⟨w, _, hPair, hPairBound⟩ := exists_canonicalConvolutionKernel hG f
  obtain ⟨B, hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  let L := B * ∫ a, ‖f a‖ ∂dg
  have hL : 0 ≤ L := mul_nonneg hB₀ (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨C, hC, hBound⟩ := hMass (tsupport f * (tsupport f)⁻¹)
    (f.hasCompactSupport.mul f.hasCompactSupport.inv)
  refine ⟨m, Real.sqrt (L * C), Real.sqrt_nonneg _, fun v x => ?_⟩
  have hval : canonicalL2Smoothing (f : AdelicGroupPoints F G → ℂ) v x = inner ℂ (w x) v :=
    ((hPair x v).2).symm
  rw [hval]
  have hHx : 1 ≤ RepresentationGrowth.adelicHeight F G rho x :=
    RepresentationGrowth.one_le_adelicHeight F G rho hN x
  have hHpow : 1 ≤ RepresentationGrowth.adelicHeight F G rho x ^ m := one_le_pow₀ hHx
  apply (norm_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hL hC), mul_assoc]
  calc
    ‖w x‖ ^ 2 ≤ L * (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG).real
        (Subtype.val ⁻¹' ((fun t => x * t * x⁻¹) '' (tsupport f * (tsupport f)⁻¹))) :=
      hPairBound x B hB
    _ ≤ L * (C * RepresentationGrowth.adelicHeight F G rho x ^ m) :=
      mul_le_mul_of_nonneg_left (hBound x) hL
    _ ≤ L * (C * (RepresentationGrowth.adelicHeight F G rho x ^ m) ^ 2) := by
      gcongr
      exact le_self_pow₀ hHpow (by decide)

/-- A function on `G(𝔸)` left invariant under `A_G G(F)` takes the same value at a point and at
the chosen representative of its class. -/
theorem out_mk_eq {E : Type*} {u : AdelicGroupPoints F G → E} (hu : ∀ c ∈ Γ, ∀ x, u (c * x) = u x)
    (z : AdelicGroupPoints F G) : u (LeftCosetSpace.mk Γ z).out = u z := by
  have h := Quotient.out_eq (LeftCosetSpace.mk Γ z)
  have hmem : z * ((LeftCosetSpace.mk Γ z).out)⁻¹ ∈ Γ :=
    (LeftCosetSpace.mk_eq_mk_iff Γ _ _).mp h
  have hz : z = (z * ((LeftCosetSpace.mk Γ z).out)⁻¹) * (LeftCosetSpace.mk Γ z).out := by
    group
  conv_rhs => rw [hz]
  exact (hu _ hmem _).symm

include hG in
/-- Two continuous functions on `G(𝔸)`, left invariant under `A_G G(F)`, whose restrictions to
representatives agree almost everywhere on `[G]`, are equal. -/
theorem eq_of_ae_eq_out {u₁ u₂ : AdelicGroupPoints F G → ℂ} (h₁ : Continuous u₁)
    (h₂ : Continuous u₂) (hi₁ : ∀ c ∈ Γ, ∀ x, u₁ (c * x) = u₁ x)
    (hi₂ : ∀ c ∈ Γ, ∀ x, u₂ (c * x) = u₂ x)
    (hae : (fun y : CanonicalQuotient F G => u₁ y.out) =ᵐ[μ] fun y => u₂ y.out) : u₁ = u₂ := by
  let := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  have := canonicalMeasure_isOpenPosMeasure F G centralSplitTorusCharacter hG
  let v₁ := LeftCosetSpace.lift Γ u₁ (fun c x => hi₁ c c.2 x)
  let v₂ := LeftCosetSpace.lift Γ u₂ (fun c x => hi₂ c c.2 x)
  have hv₁ : ∀ y, v₁ y = u₁ y.out := fun y => by
    conv_lhs => rw [← Quotient.out_eq y]
    rfl
  have hv₂ : ∀ y, v₂ y = u₂ y.out := fun y => by
    conv_lhs => rw [← Quotient.out_eq y]
    rfl
  have hc₁ : Continuous v₁ := LeftCosetSpace.continuous_lift Γ u₁ _ h₁
  have hc₂ : Continuous v₂ := LeftCosetSpace.continuous_lift Γ u₂ _ h₂
  have hv : v₁ = v₂ := (Continuous.ae_eq_iff_eq μ hc₁ hc₂).mp (by
    filter_upwards [hae] with y hy
    rw [hv₁, hv₂, hy])
  funext x
  exact congrFun hv (LeftCosetSpace.mk Γ x)

/-- The class of a right translate: if `v` is represented by `u ∘ out` for a left
`A_G G(F)`-invariant `u`, then `R(g) v` is represented by `y ↦ u(y.out g)`. -/
theorem canonicalL2RightAction_ae_eq {u : AdelicGroupPoints F G → ℂ}
    (hu : ∀ c ∈ Γ, ∀ x, u (c * x) = u x) (g : AdelicGroupPoints F G) {v : Lp ℂ 2 μ}
    (hv : v =ᵐ[μ] fun y => u y.out) :
    (canonicalL2RightAction F G centralSplitTorusCharacter hG g v : CanonicalQuotient F G → ℂ)
      =ᵐ[μ] fun y => u (y.out * g) := by
  let r := canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG
  refine (Lp.coeFn_compMeasurePreserving v (r g)).trans ?_
  have h2 := (r g).quasiMeasurePreserving.ae_eq_comp hv
  refine h2.trans (Filter.Eventually.of_forall fun y => ?_)
  change u (LeftCosetSpace.rightTranslate Γ g y).out = u (y.out * g)
  conv_lhs => rw [← Quotient.out_eq y]
  exact out_mk_eq hu (y.out * g)

/-- The right regular representation of `G(𝔸)` on `L²([G])` preserves inner products. -/
theorem inner_canonicalL2RightAction (g : AdelicGroupPoints F G) (x y : Lp ℂ 2 μ) :
    inner ℂ (canonicalL2RightAction F G centralSplitTorusCharacter hG g x)
      (canonicalL2RightAction F G centralSplitTorusCharacter hG g y) = inner ℂ x y :=
  (rationalQuotientL2RightTranslate F G _
    (canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG) g).inner_map_map x y

/-- The orthogonal projection onto a closed invariant subspace commutes with the right regular
representation. -/
theorem starProjection_canonicalL2RightAction (V : Submodule ℂ (Lp ℂ 2 μ))
    [V.HasOrthogonalProjection]
    (hV : ∀ (g : AdelicGroupPoints F G), ∀ x ∈ V,
      canonicalL2RightAction F G centralSplitTorusCharacter hG g x ∈ V)
    (g : AdelicGroupPoints F G) (x : Lp ℂ 2 μ) :
    V.starProjection (canonicalL2RightAction F G centralSplitTorusCharacter hG g x) =
      canonicalL2RightAction F G centralSplitTorusCharacter hG g (V.starProjection x) := by
  let R := canonicalL2RightAction F G centralSplitTorusCharacter hG
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hV g _ (V.starProjection_apply_mem x))
  intro w hw
  have hsub : R g x - R g (V.starProjection x) = R g (x - V.starProjection x) := by
    rw [map_sub]
  have hw' : w = R g (R g⁻¹ w) := by
    change w = (R g * R g⁻¹) w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hsub, hw', inner_canonicalL2RightAction]
  exact (Submodule.inner_right_of_mem_orthogonal (hV g⁻¹ w hw)
    (Submodule.sub_starProjection_mem_orthogonal x)).symm ▸ by
      rw [← inner_conj_symm, Submodule.inner_right_of_mem_orthogonal (hV g⁻¹ w hw)
        (Submodule.sub_starProjection_mem_orthogonal x), map_zero]

/-- The orthogonal projection onto a closed invariant subspace commutes with the integrated
action. -/
theorem starProjection_canonicalL2IntegratedAction (V : Submodule ℂ (Lp ℂ 2 μ))
    [V.HasOrthogonalProjection]
    (hV : ∀ (g : AdelicGroupPoints F G), ∀ x ∈ V,
      canonicalL2RightAction F G centralSplitTorusCharacter hG g x ∈ V)
    (h : AdelicGroupPoints F G → ℂ) (hh : Integrable h dg) (x : Lp ℂ 2 μ) :
    V.starProjection (canonicalL2IntegratedAction hG h hh x) =
      canonicalL2IntegratedAction hG h hh (V.starProjection x) := by
  have hint : Integrable
      (fun g => h g • canonicalL2RightAction F G centralSplitTorusCharacter hG g x) dg :=
    Langlands.Analysis.isometricActionIntegrand_integrable dg (canonicalL2BoundedRightAction hG)
      (fun g φ => norm_canonicalL2RightAction hG g φ)
      (fun φ => (continuous_canonicalL2RightAction_orbit hG φ).aestronglyMeasurable) h hh x
  rw [canonicalL2IntegratedAction_apply, canonicalL2IntegratedAction_apply,
    ← ContinuousLinearMap.integral_comp_comm V.starProjection hint]
  congr 1
  funext g
  rw [map_smul]
  congr 1
  exact starProjection_canonicalL2RightAction hG V hV g x

include hG in
/-- Null sets of `[G]` pull back to Haar-null sets of `G(𝔸)` (Weil's formula for measurable
nonnegative functions). -/
theorem quasiMeasurePreserving_mk :
    QuasiMeasurePreserving (LeftCosetSpace.mk Γ) dg μ := by
  let := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  have hΓ := isClosed_canonicalRationalSubgroup F G centralSplitTorusCharacter hG
  let := canonicalSubgroupHaarMeasure_isHaarMeasure F G centralSplitTorusCharacter hG
  refine ⟨LeftCosetSpace.measurable_mk Γ, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply (LeftCosetSpace.measurable_mk Γ) hs]
  have hm : MeasurableSet (LeftCosetSpace.mk Γ ⁻¹' s) := LeftCosetSpace.measurable_mk Γ hs
  have hW := IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal hΓ
    (canonicalMeasure_isCompatible F G centralSplitTorusCharacter hG)
    ((LeftCosetSpace.mk Γ ⁻¹' s).indicator 1) (measurable_one.indicator hm)
  rw [lintegral_indicator_one hm] at hW
  rw [hW]
  have hz : quotientAverageENNReal Γ (canonicalSubgroupHaarMeasure F G centralSplitTorusCharacter hG)
      ((LeftCosetSpace.mk Γ ⁻¹' s).indicator 1) =ᵐ[μ] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs0] with q hq
    induction q using Quotient.inductionOn with
    | h g =>
      rw [quotientAverageENNReal_mk]
      have hzero : (fun h : Γ => (LeftCosetSpace.mk Γ ⁻¹' s).indicator
          (1 : AdelicGroupPoints F G → ℝ≥0∞) (h.val * g)) = fun _ => 0 := by
        funext h
        apply Set.indicator_of_notMem
        change LeftCosetSpace.mk Γ (h.val * g) ∉ s
        rw [LeftCosetSpace.mk_subgroup_mul Γ h g]
        exact hq
      rw [hzero, lintegral_zero]
      rfl
  rw [lintegral_congr_ae hz]
  exact lintegral_zero

include hG in
/-- If a class `v` of `L²([G])` is represented by `u ∘ out` for a left `A_G G(F)`-invariant `u`,
then the pullback of `v` agrees with `u` Haar-almost everywhere on `G(𝔸)`. -/
theorem canonicalL2Pullback_ae_eq {u : AdelicGroupPoints F G → ℂ}
    (hu : ∀ c ∈ Γ, ∀ x, u (c * x) = u x) {v : Lp ℂ 2 μ} (hv : v =ᵐ[μ] fun y => u y.out) :
    canonicalL2Pullback v =ᵐ[dg] u :=
  (QuasiMeasurePreserving.ae_eq_comp (quasiMeasurePreserving_mk hG) hv).trans
    (Filter.Eventually.of_forall fun x => out_mk_eq hu x)

include hG in
/-- In the situation of `canonicalL2Pullback_ae_eq`, smoothing `v` is right convolution of `u`. -/
theorem canonicalL2Smoothing_eq_rightConvolution {u : AdelicGroupPoints F G → ℂ}
    (hu : ∀ c ∈ Γ, ∀ x, u (c * x) = u x) {v : Lp ℂ 2 μ} (hv : v =ᵐ[μ] fun y => u y.out)
    (h : AdelicGroupPoints F G → ℂ) :
    canonicalL2Smoothing h v = rightConvolution F G h u := by
  funext x
  unfold canonicalL2Smoothing rightConvolution
  apply integral_congr_ae
  have hx := (measurePreserving_mul_left dg x).quasiMeasurePreserving.ae_eq_comp
    (canonicalL2Pullback_ae_eq hG hu hv)
  filter_upwards [hx] with a ha
  rw [show canonicalL2Pullback v (x * a) = u (x * a) from ha]

include hG in
/-- Smoothing by a continuous compactly supported kernel gives a function of moderate growth for
the adelic norm of a closed matrix embedding. For `N = 0`, `G(𝔸)` is a single point. -/
theorem hasModerateGrowthFunction_canonicalL2Smoothing {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (f : C_c(AdelicGroupPoints F G, ℂ)) (v : Lp ℂ 2 μ) :
    HasModerateGrowthFunction F G rho (canonicalL2Smoothing (f : AdelicGroupPoints F G → ℂ) v) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    refine ⟨‖canonicalL2Smoothing (f : AdelicGroupPoints F G → ℂ) v 1‖ + 1, by positivity, 0,
      fun g => ?_⟩
    rw [Real.rpow_zero, mul_one, Subsingleton.elim g 1]
    linarith
  · obtain ⟨m, C, hC, hbound⟩ := exists_canonicalL2Smoothing_bound hG rho hN hrho f
    set c : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) with hc
    have hc0 : 0 ≤ c := by positivity
    refine ⟨C * c ^ m * ‖v‖ + 1, by positivity, m, fun g => ?_⟩
    have h1 := hbound v g
    rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm, mul_pow] at h1
    have hsn := RepresentationGrowth.adelicSourceNorm_pos F G rho hN g
    rw [Real.rpow_natCast]
    calc ‖canonicalL2Smoothing (f : AdelicGroupPoints F G → ℂ) v g‖
        ≤ C * (c ^ m * RepresentationGrowth.adelicSourceNorm F G rho g ^ m) * ‖v‖ := h1
      _ = (C * c ^ m * ‖v‖) * RepresentationGrowth.adelicSourceNorm F G rho g ^ m := by ring
      _ ≤ (C * c ^ m * ‖v‖ + 1) * RepresentationGrowth.adelicSourceNorm F G rho g ^ m := by
        gcongr
        linarith

end Reductive

end RestrictionSplitCentre

end Langlands.Global
