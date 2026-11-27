import Langlands.Global.AdelicFixedProfileReproduction
import Langlands.Global.AdelicHilbertCompactProfiles
import Langlands.Global.AdelicGroupPolish
import Langlands.Analysis.NormalizedAverageApproximation
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof
import Langlands.Representation.Archimedean.CompactSmoothAverage
import Langlands.Representation.Archimedean.ProductSmoothInfinitesimalCharacter
import Langlands.Representation.Unitary.IntegratedIsometricSmoothDensityProof
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Smooth reproduction of compact-finite vectors in irreducible adelic Hilbert representations -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Set
open scoped CategoryTheory.MonObj Manifold ContDiff InnerProductSpace TensorProduct Pointwise

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 850000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Archimedean
open Langlands.Analysis Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints
open Langlands.Analysis.NormalizedAverage

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "A" => AdelicGroupPoints F G
local notation "M" => InfiniteAdelicGroupPoints F G
local notation "B" => FiniteAdelicGroupPoints F G
local notation "ιi" => ContinuousMonoidHom.toMonoidHom (ofInfinite F G)
local notation "ιf" => ContinuousMonoidHom.toMonoidHom (ofFinite F G)
local notation "I" => 𝓘(ℝ, smoothModel F d)
local notation "dm" => (Measure.haar : Measure M)

private theorem adelicFactors_generate (x : A) : ∃ a : M, ∃ b : B, x = ιi a * ιf b := by
  refine ⟨infinite F G x, finite F G x, ?_⟩
  change x = pair F G (infinite F G x) 1 * pair F G 1 (finite F G x)
  rw [AdelicGroupPoints.pair_mul, mul_one, one_mul, pair_projections]

/-- The adjoint-invariance theorem for the actual center supplies Segal's scalar action. -/
theorem adelicSmoothCenterActsByScalar (hG : IsConnectedReductive G)
    (π : A →* (H →L[ℂ] H)) (hu : ∀ g u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ)
    (hirr : IsTopologicallyIrreducible π) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
    ProductSmoothVectors.smoothSubspace (smoothModel F d) ιi ιf π ≠ ⊥ →
    ∀ z : AdelicEnvelopingCenter F G hsmooth, ∃ c : ℂ,
      ∀ v : ProductSmoothVectors.smoothSubspace (smoothModel F d) ιi ιf π,
        (SmoothVectorEnveloping.envelopingAction (π.comp ιi) hcalc z.val ⟨v, v.property.1⟩ : H) =
          c • (v : H) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  intro hne z
  exact ProductSmoothVectors.exists_smul_of_adjointInvariant ιi ιf π (factors_commute F G)
    hcalc adelicFactors_generate hu hirr hne z.val
    (fun g => ⟨adelicEnvelopingConjugation F G hsmooth g,
      adelicEnvelopingConjugation_ι_tmul F G hsmooth g,
      adelicEnvelopingCenterConjugation F G hsmooth hG g z.val z.property⟩)

/-- Continuous linear forms are distributions of order zero for the product action. -/
theorem isDistributionForm_continuousLinearMap (π : A →* (H →L[ℂ] H)) (ℓ : H →L[ℂ] ℂ) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    ProductSmoothVectors.IsDistributionForm («A» := smoothModel F d) ιi ιf π ℓ.toLinearMap := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  intro L hL
  refine ⟨{[]}, ‖ℓ‖, fun v hv hvL => ?_⟩
  simpa using ℓ.le_opNorm v

variable (π : AdelicGroupPoints F G →* (H →L[ℂ] H))

theorem continuous_action_of_isometric_orbits
    {S : Type*} [Group S] [TopologicalSpace S] (R : S →* (H →L[ℂ] H))
    (hnorm : ∀ x v, ‖R x v‖ = ‖v‖) (hcont : ∀ v : H, Continuous fun x : S => R x v) :
    IsContinuousRepresentation R := by
  rw [IsContinuousRepresentation]
  refine continuous_iff_continuousAt.mpr fun p => ?_
  let f := fun x : S × H => R x.1 x.2
  have hh (x : S × H) : dist (f x) (f p) ≤ dist x.2 p.2 + dist (R x.1 p.2) (R p.1 p.2) := by
    refine (dist_triangle _ (R x.1 p.2) _).trans ?_
    rw [show dist (R x.1 x.2) (R x.1 p.2) = dist x.2 p.2 by rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm]]
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have h₁ := (Metric.tendsto_nhds.mp (continuous_snd.continuousAt (x := p))) (ε / 2) (half_pos hε)
  have h₂ := (Metric.tendsto_nhds.mp (((hcont p.2).comp continuous_fst).continuousAt (x := p)))
    (ε / 2) (half_pos hε)
  exact (h₁.and h₂).mono fun x ⟨hx, hy⟩ => (hh x).trans_lt (by
    simp only [Function.comp_apply] at hy
    linarith)

/-- Reproduction by a smooth compact kernel on the infinite group at a fixed finite level. -/
def HasArchimedeanSmoothConvolution (L : Subgroup B) (w : H) : Prop := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  exact ∃ (h : M → ℂ) (u : H), HasCompactSupport h ∧ ContMDiff I 𝓘(ℝ, ℂ) ∞ h ∧
    (∀ l ∈ L, π (ofFinite F G l) u = u) ∧
    w = (∫ x, h x • π (ofInfinite F G x) u ∂(Measure.haar : Measure M))

include hcalc in
/-- A nonzero compact-finite vector fixed at an open finite level is an archimedean
smooth compact convolution of a vector fixed at that same level. -/
theorem exists_archimedean_smooth_convolution_of_adelicFinite (hG : IsConnectedReductive G)
    (hu : ∀ g u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ)
    (hnorm : ∀ g v, ‖π g v‖ = ‖v‖) (hcont : ∀ v : H, Continuous fun g : A => π g v)
    (hirr : IsTopologicallyIrreducible π)
    (K : Subgroup M) (hK : CompactIwasawa.IsMaximalCompact K)
    (L : Subgroup B) (hL : IsOpen (L : Set B)) (w : H) (hw0 : w ≠ 0)
    (hwK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π (ιi k.val) w)))
    (hwL : ∀ l ∈ L, π (ιf l) w = w) :
    HasArchimedeanSmoothConvolution hsmooth π L w := by
  classical
  unfold HasArchimedeanSmoothConvolution
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  letI : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  let dk : Measure K := Measure.haar
  let j := (ιi).comp K.subtype
  let R := π.comp ιi
  let σ := π.comp ιf
  let U := SmoothInvariantSubspace.fixedSubspace σ L
  have hU := SmoothInvariantSubspace.isClosed_fixedSubspace σ L
  have hcomm : ∀ x l v, R x (σ l v) = σ l (R x v) :=
    fun x l v => (ProductSmoothVectors.finite_comm ιi ιf π (factors_commute F G) l x v).symm
  have hRc (v : H) : Continuous fun g : M => R g v := (hcont v).comp (ofInfinite F G).continuous
  have hRn (g : M) (v : H) : ‖R g v‖ = ‖v‖ := hnorm (ιi g) v
  have hRmeas (v : H) : AEStronglyMeasurable (fun g : M => R g v) dm :=
    (hRc v).stronglyMeasurable.aestronglyMeasurable
  obtain ⟨E, hEfin, hE, hEleft, hwE⟩ := exists_hilbertCompactProfiles π K hcont w hwK
  letI : FiniteDimensional ℂ E := hEfin
  let T := hilbertCompactProfileSubspace π K E ⊓ U
  have hT : IsClosed (T : Set H) := (isClosed_hilbertCompactProfileSubspace π K E).inter hU
  letI : CompleteSpace T := hT.completeSpace_coe
  have hwT : w ∈ T := ⟨hwE, fun l => hwL l l.property⟩
  obtain ⟨a, haout, hafix⟩ := exists_hilbertCompactProfileProjection π K dk hcont E hE hEleft
  have hai : Integrable a dk := a.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P := integratedIsometricAction dk (π.comp j) (fun k v => hnorm _ v)
    (fun v => ((hRc v).comp continuous_subtype_val).stronglyMeasurable.aestronglyMeasurable) a hai
  have hPT (v : H) (hv : v ∈ U) : P v ∈ T := by
    refine ⟨haout v, ?_⟩
    exact integral_mem_of_isClosed U hU
      ((a.continuous.smul ((hRc v).comp continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (fun k => U.smul_mem _ (SmoothInvariantSubspace.fixedSubspace_invariant σ L R hcomm k v hv))
  let W := ProductSmoothVectors.smoothSubspace (smoothModel F d) ιi ιf π
  have hdense (v : H) (hv : v ∈ T) : v ∈ closure {x | x ∈ T ∧ x ∈ W} := by
    let R₀ := SmoothInvariantSubspace.fixedRestriction σ L R hcomm
    have hR₀ (v₀ : U) : Continuous fun g : M => R₀ g v₀ := (hRc v₀).subtype_mk _
    have hd := integratedIsometricSmoothDensity (smoothModel F d) M U dm R₀
      (fun g u => hRn g u) (fun u => (hR₀ u).stronglyMeasurable.aestronglyMeasurable) hR₀
    have hi : Continuous (fun x : U => P (x : H)) := P.continuous.comp continuous_subtype_val
    have hv₀ : P v ∈ closure ((fun x : U => P (x : H)) ''
        (Langlands.Archimedean.smoothVectors I R₀ : Set U)) :=
      mem_closure_image (hi.continuousAt (x := (⟨v, hv.2⟩ : U))) (hd ⟨v, hv.2⟩)
    have hvP : P v = v := hafix v hv.1
    rw [hvP] at hv₀
    refine closure_mono ?_ hv₀
    rintro _ ⟨u, hu', rfl⟩
    have hsm := (SmoothInvariantSubspace.isSmoothVector_fixedRestriction_iff σ L R hcomm I u).mp hu'
    have hPsm : Langlands.Archimedean.IsSmoothVector I R (P u) :=
      CompactSmoothAverage.isSmoothVector_orbitIntegral R dk a
        ⟨Subtype.val, continuous_subtype_val⟩ hsm
    have hout := hPT u u.property
    exact ⟨hout, hPsm, L, hL, fun l hl => hout.2 ⟨l, hl⟩⟩
  have hWne : W ≠ ⊥ := by
    intro hz
    have h : w ∈ closure ({0} : Set H) := closure_mono (fun x hx => by
      have hx' : x ∈ W := hx.2
      rw [hz, Submodule.mem_bot] at hx'
      exact hx') (hdense w hwT)
    rw [isClosed_singleton.closure_eq, Set.mem_singleton_iff] at h
    exact hw0 h
  obtain ⟨z, hrepro⟩ := exists_reproducingKernel_of_centerEigenvalue F G hsmooth hcalc hG K hK E
  obtain ⟨c, hc⟩ := adelicSmoothCenterActsByScalar hsmooth hcalc hG π hu hirr hWne z
  obtain ⟨κ, hκ, hκc, hκrep⟩ := hrepro c
  have hκi : Integrable κ dm := hκ.integrable_of_hasCompactSupport hκc
  let Q := integratedIsometricAction dm R hRn hRmeas κ hκi
  have hQsm (v : H) (hv : v ∈ T) (hvs : v ∈ W) : Q v = v := by
    let ℓ := innerSL ℂ (Q v - v)
    let f : M → ℂ := fun x => ℓ (R x v)
    have hℓ := isDistributionForm_continuousLinearMap hsmooth π ℓ
    have hgen := adelicFactors_generate (F := F) (G := G)
    have hf0 := ProductSmoothVectors.coefficient_contMDiff ιi ιf π (factors_commute F G)
      hu ℓ.toLinearMap hℓ v hvs (1 : B)
    have hf : f ∈ InfinitePlotSmoothFunctions F G := by
      apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
      change ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x => ℓ.toLinearMap (π (ιi x) v))
      simpa only [map_one, mul_one] using hf0
    let b : InfinitePlotSmoothFunctions F G := ⟨f, hf⟩
    have hpro (x : M) : Langlands.Automorphic.rightCompactProfile K x b.val ∈ E := by
      have hp := (mem_hilbertCompactProfileSubspace π K E v).mp hv.1 (ℓ.comp (R x))
      convert hp using 1
      funext k
      change ℓ (R (x * k.val) v) = ℓ (R x (R k.val v))
      rw [map_mul, mul_apply_eq_comp]
    have hD : plotSmoothCenterAction F G hsmooth hcalc z b = c • b := by
      have hsmem (g : M → ℂ) (hg : ContMDiff I 𝓘(ℝ, ℂ) ∞ g) : g ∈ InfinitePlotSmoothFunctions F G :=
        (isPlotSmooth_iff_contMDiff F G hsmooth g).mpr hg
      have hΘ (X : GroupLieAlgebra I M) (g : InfinitePlotSmoothFunctions F G) :
          ((plotSmoothEnvelopingAction F G hsmooth hcalc
            (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) g : InfinitePlotSmoothFunctions F G) : M → ℂ) =
            groupDirectionalValue I X g := by
        rw [plotSmoothEnvelopingAction_real_generator]
        rfl
      have he : (fun x : M => ℓ.toLinearMap (π (ιi x * ιf (1 : B)) v)) = f := by
        simp only [f, map_one, mul_one, MonoidHom.comp_apply, R]
        rfl
      have hdiff := ProductSmoothVectors.coefficient_envelopingAction ιi ιf π (factors_commute F G)
        hcalc hu ℓ.toLinearMap hℓ _ hsmem (plotSmoothEnvelopingAction F G hsmooth hcalc)
        hΘ v hvs (1 : B) z.val (he.symm ▸ hf)
      have hv' := hc ⟨v, hvs⟩
      have hsub : (⟨_, he.symm ▸ hf⟩ : InfinitePlotSmoothFunctions F G) = b := Subtype.ext he
      rw [hsub] at hdiff
      apply Subtype.ext
      change ((plotSmoothEnvelopingAction F G hsmooth hcalc z.val b : InfinitePlotSmoothFunctions F G) : M → ℂ) = _
      rw [hdiff]
      funext x
      rw [show (SmoothVectorEnveloping.envelopingAction R hcalc z.val ⟨v, hvs.1⟩ : H) = c • v from hv']
      simp only [map_one, mul_one, map_smul]
      rfl
    have heval := hκrep b hD hpro
    have he : ℓ (Q v) = ℓ v := by
      change ℓ (∫ x, κ x • R x v ∂dm) = _
      rw [← ℓ.integral_comp_comm (isometricActionIntegrand_integrable dm R hRn hRmeas κ hκi v)]
      simpa only [b, f, map_one, one_apply_eq_self, Function.comp_apply, map_smul, smul_eq_mul, mul_comm] using heval.symm
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (show ℓ (Q v - v) = 0 by rw [map_sub, he, sub_self]))
  have hQ (v : H) (hv : v ∈ T) : Q v = v :=
    closure_minimal (s := {x | x ∈ T ∧ x ∈ W}) (t := {x | Q x = x})
      (fun _ hx => hQsm _ hx.1 hx.2) (isClosed_eq Q.continuous continuous_id) (hdense v hv)
  let S := tsupport κ
  have hS : IsCompact S := hκc
  let ε : ℝ := (2 * (‖P‖ + 1) * ((dm).real S + 1))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨g, hga, hgs⟩ := hκ.exists_contMDiff_approx I ⊤ (continuous_const (y := ε)) (fun _ => hε)
  let k : M → ℂ := g
  have hk : ContMDiff I 𝓘(ℝ, ℂ) ∞ k := g.contMDiff
  have hkc : HasCompactSupport k := HasCompactSupport.of_support_subset_isCompact hS (hgs.trans (subset_tsupport _))
  have hki : Integrable k dm := hk.continuous.integrable_of_hasCompactSupport hkc
  let V := integratedIsometricAction dm R hRn hRmeas k hki
  have hVU (v : H) (hv : v ∈ U) : V v ∈ U :=
    integral_mem_of_isClosed U hU (isometricActionIntegrand_integrable dm R hRn hRmeas k hki v)
      (fun x => U.smul_mem _ (SmoothInvariantSubspace.fixedSubspace_invariant σ L R hcomm x v hv))
  let J : T →L[ℂ] T := ((P.comp V).restrict (fun v hv => hPT _ (hVU v hv.2)))
  have hbound (v : H) : ‖V v - Q v‖ ≤ (ε * (dm).real S) * ‖v‖ := by
    dsimp only [V, Q, integratedIsometricAction_apply]
    rw [← integral_sub (isometricActionIntegrand_integrable dm R hRn hRmeas k hki v)
      (isometricActionIntegrand_integrable dm R hRn hRmeas κ hκi v)]
    simp_rw [← sub_smul]
    have hSupp : Function.support (fun x => (k x - κ x) • R x v) ⊆ S := by
      intro x hx
      by_contra hn
      have hκ0 := image_eq_zero_of_notMem_tsupport hn
      have hk0 : k x = 0 := by
        by_contra h
        exact hn (hgs.trans (subset_tsupport _) h)
      apply hx
      change (k x - κ x) • R x v = 0
      rw [hk0, hκ0, sub_zero, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => not_not.mp (fun h => hx (hSupp h)))]
    letI : IsFiniteMeasure ((dm).restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    calc
      _ ≤ (ε * ‖v‖) * ((dm).restrict S).real univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
          rw [norm_smul, hRn, ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_right (hga x).le (norm_nonneg _))
      _ = _ := by rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def]; ring
  have hJ : ‖1 - J‖ < 1 := by
    have h₀ : ‖1 - J‖ ≤ ‖P‖ * (ε * (dm).real S) := by
      refine ContinuousLinearMap.opNorm_le_bound (1 - J) (by positivity) ?_
      intro v
      have hp : P (Q v) = (v : H) := (congrArg P (hQ v v.property)).trans (hafix _ v.property.1)
      change ‖(v : H) - P (V v)‖ ≤ _
      calc
        ‖(v : H) - P (V v)‖ = ‖P (V v - Q v)‖ := by rw [map_sub, hp, norm_sub_rev]
        _ ≤ ‖P‖ * ‖V v - Q v‖ := P.le_opNorm _
        _ ≤ ‖P‖ * (ε * (dm).real S) * ‖v‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hbound v) (norm_nonneg _)
    refine lt_of_le_of_lt h₀ ?_
    dsimp only [ε]
    have hp : 0 ≤ ‖P‖ := norm_nonneg _
    have hm : 0 ≤ (dm).real S := measureReal_nonneg
    have ht : 0 < 2 * (‖P‖ + 1) * ((dm).real S + 1) := by positivity
    field_simp
    nlinarith
  have hUnit : IsUnit J := by
    simpa only [sub_sub_cancel] using
      isUnit_one_sub_of_norm_lt_one (R := T →L[ℂ] T) (x := 1 - J) hJ
  obtain ⟨u, hu'⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hUnit).2 ⟨w, hwT⟩
  let h (x : M) : ℂ := ∫ k' : K, a k' * k (k'.val⁻¹ * x) ∂dk
  have hhd : ContMDiff I 𝓘(ℝ, ℂ) ∞ h := by
    let inc : C(K, M) := ⟨Subtype.val, continuous_subtype_val⟩
    have hc : ContMDiff ((I).prod I) 𝓘(ℝ, ℂ) ∞ (fun p : M × M => k (p.2⁻¹ * p.1)) :=
      hk.comp (contMDiff_snd.inv.mul contMDiff_fst)
    exact Langlands.Analysis.CompactManifoldVectorIntegral.contMDiff_weightedIntegral dk a inc hc
  have hhc : HasCompactSupport h := by
    apply HasCompactSupport.of_support_subset_isCompact (hK.1.mul hkc)
    intro x hx
    by_contra hn
    apply hx
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun s => by
      have hn' : s.val⁻¹ * x ∉ tsupport k := fun hs => hn ⟨s.val, s.property, _, hs, by simp⟩
      change a s * k (s.val⁻¹ * x) = 0
      rw [image_eq_zero_of_notMem_tsupport hn', mul_zero]
  refine ⟨h, u, hhc, hhd, fun l hl => u.property.2 ⟨l, hl⟩, ?_⟩
  have hval : w = P (V u) := (congrArg Subtype.val hu').symm
  rw [hval]
  -- The compact average precedes the archimedean convolution in the operator product.
  let f (s : K) (x : M) : H := (a s * k (s.val⁻¹ * x)) • R x u
  have hfc : Continuous (Function.uncurry f) :=
    ((a.continuous.comp continuous_fst).mul
      (hk.continuous.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))).smul
      ((hRc u).comp continuous_snd)
  have hfs : HasCompactSupport (Function.uncurry f) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ.prod (hK.1.mul hkc))
    rintro ⟨s, x⟩ hx
    have hs : s.val⁻¹ * x ∈ tsupport k := by
      by_contra hn
      exact hx (by simp [Function.uncurry, f, image_eq_zero_of_notMem_tsupport hn])
    exact ⟨Set.mem_univ _, ⟨s.val, s.property, _, hs, by simp⟩⟩
  calc
    P (V u) = ∫ s : K, ∫ x, f s x ∂dm ∂dk := by
      change (∫ s : K, a s • R s.val (∫ x, k x • R x u ∂dm) ∂dk) = _
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        change a s • R s.val (∫ x, k x • R x u ∂dm) = ∫ x, f s x ∂dm
        rw [← (R s.val).integral_comp_comm
          (isometricActionIntegrand_integrable dm R hRn hRmeas k hki u), ← integral_smul,
          ← integral_mul_left_eq_self (f s) s.val]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [map_smul, smul_smul, f, inv_mul_cancel_left, map_mul,
            mul_apply_eq_comp]
    _ = ∫ x, h x • R x u ∂dm := by
      rw [integral_integral_swap_of_hasCompactSupport hfc hfs]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => integral_smul_const _ _

end Langlands.Global
