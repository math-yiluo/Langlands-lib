import Langlands.Global.AdelicFiniteProjectionReduction
import Langlands.Global.AdelicCanonicalL2Smoothing
import Langlands.Global.AdelicSmoothReproducingKernel
import Langlands.Global.AdelicRightConvolutionEnveloping
import Langlands.Analysis.FiniteSubspaceInterpolation

/-! # Projections of square-integrable functions of fixed type are automorphic forms

`squareIntegrableProjectionAutomorphy` proves `SquareIntegrableProjectionAutomorphyStatement`.
A smooth kernel `β` reproduces `φ` (Harish-Chandra 1966, §8, Theorem 1), so `R(β) f = f`. The
projection `w` of `f` onto a closed invariant subspace satisfies `R(β) w = w`, and the smoothing
`ψ` of `w` by `β` is a continuous representative of `w` with smooth slices and moderate growth
(Mœglin–Waldspurger I.2.5). The type `(J, L, E)` passes from `φ` to `ψ` through relations in
`L²([G])` between translates and through the transfer of central derivatives to the kernel
(Getz–Hahn, proof of Corollary 6.2.5). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

section Lemmas

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A function left invariant under `A_G` and under `G(F)` is left invariant under the subgroup
`A_G G(F)` they generate. -/
theorem isLeftInvariant_canonicalRationalSubgroup {u : AdelicGroupPoints F G → ℂ}
    (h₁ : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) u)
    (h₂ : IsLeftInvariantUnder F G (rationalSubgroup F G) u) :
    ∀ c ∈ RestrictionSplitCentre.canonicalRationalSubgroup F G, ∀ x, u (c * x) = u x := by
  let S : Subgroup (AdelicGroupPoints F G) :=
    { carrier := {c | ∀ x, u (c * x) = u x}
      mul_mem' := fun {a b} ha hb x => by
        change u (a * b * x) = u x
        rw [mul_assoc, ha, hb]
      one_mem' := fun x => by
        change u (1 * x) = u x
        rw [one_mul]
      inv_mem' := fun {a} ha x => by
        rw [← ha (a⁻¹ * x), mul_inv_cancel_left] }
  have hle : RestrictionSplitCentre.canonicalRationalSubgroup F G ≤ S := by
    unfold RestrictionSplitCentre.canonicalRationalSubgroup RestrictionSplitCentre.rationalSubgroup
    exact sup_le (fun c hc => h₁ c hc) (fun c hc => h₂ c hc)
  exact fun c hc => hle hc

omit [LocallyOfFiniteType G.X.hom] in
/-- A function all of whose functions `k ↦ u(g k)` on `K_∞` lie in one finite-dimensional space
`E` is `K_∞`-finite. -/
theorem isInfiniteSubgroupFiniteFunction_of_mem {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {E : Submodule ℂ (Kinf → ℂ)} [FiniteDimensional ℂ E] {u : AdelicGroupPoints F G → ℂ}
    (hu : ∀ g, (fun k : Kinf => u (g * ofInfinite F G k)) ∈ E) :
    IsInfiniteSubgroupFiniteFunction F G Kinf u := by
  let Θ : Module.Dual ℂ E →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    { toFun := fun ℓ g => ℓ ⟨fun k => u (g * ofInfinite F G k), hu g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : Submodule.span ℂ (Set.range fun k : Kinf =>
      fun g : AdelicGroupPoints F G => u (g * ofInfinite F G k)) ≤ LinearMap.range Θ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨(LinearMap.proj k : (Kinf → ℂ) →ₗ[ℂ] ℂ).comp E.subtype, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end Lemmas

set_option maxHeartbeats 400000 in
open RestrictionSplitCentre in
/-- **The projections of a square-integrable function of fixed type are automorphic forms of
the same type.** The form is `canonicalL2Smoothing β (V.starProjection f)` for a test kernel `β`
reproducing `φ`. The proof uses the reproducing kernel and differentiation identities of
Getz–Hahn 2024, Theorem 6.2.4 and the proof of Corollary 6.2.5, and the folding estimate of
Mœglin–Waldspurger 1995, I.2.4–I.2.5. -/
theorem squareIntegrableProjectionAutomorphy : SquareIntegrableProjectionAutomorphyStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho J hJ L hLo E hE φ hφΓ hφA hφs hφL
    hφJ hφE f hf V _ hV
  classical
  have := hE
  set R := canonicalL2RightAction F G centralSplitTorusCharacter hG with hR
  have hφinv := isLeftInvariant_canonicalRationalSubgroup hφA hφΓ
  have hφK : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ :=
    isInfiniteSubgroupFiniteFunction_of_mem hφE
  obtain ⟨β, hβ, hβφ⟩ := exists_adelicTestFunction_rightConvolution_eq hG hKmax rho hrho hsmooth
    hcalc φ hφs hφK ⟨J, hJ, hφJ⟩
  have hβi : Integrable β (Measure.haar : Measure (AdelicGroupPoints F G)) :=
    hβ.1.1.integrable_of_hasCompactSupport hβ.2.1
  -- integrated actions on `f` are right convolutions of `φ`
  have hint_f : ∀ (k : AdelicGroupPoints F G → ℂ)
      (hk : Integrable k (Measure.haar : Measure (AdelicGroupPoints F G))),
      (canonicalL2IntegratedAction hG k hk f : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G]
        fun y => rightConvolution F G k φ y.out := by
    intro k hk
    refine (canonicalL2IntegratedAction_ae_eq hG k hk f).trans
      (Filter.Eventually.of_forall fun y => ?_)
    rw [canonicalL2Smoothing_eq_rightConvolution hG hφinv hf k]
  have hRβf : canonicalL2IntegratedAction hG β hβi f = f := by
    apply Lp.ext
    refine (hint_f β hβi).trans ?_
    rw [hβφ]
    exact hf.symm
  set w := V.starProjection f with hw_def
  have hRβw : canonicalL2IntegratedAction hG β hβi w = w := by
    rw [hw_def, ← starProjection_canonicalL2IntegratedAction hG V hV, hRβf]
  set ψ := canonicalL2Smoothing β w with hψ_def
  have hψs : IsAdelicSmoothFunction F G ψ :=
    isAdelicSmoothFunction_canonicalL2Smoothing hG hsmooth hβ w
  have hψinv : ∀ c ∈ canonicalRationalSubgroup F G, ∀ x, ψ (c * x) = ψ x :=
    fun c hc x => canonicalL2Smoothing_mul β w c hc x
  have hψrep : (w : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G] fun y => ψ y.out := by
    have h := canonicalL2IntegratedAction_ae_eq hG β hβi w
    rw [hRβw] at h
    exact h
  have hRw : ∀ g, (R g w : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G]
      fun y => ψ (y.out * g) := fun g => canonicalL2RightAction_ae_eq hG hψinv g hψrep
  have hRf : ∀ g, (R g f : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G]
      fun y => φ (y.out * g) := fun g => canonicalL2RightAction_ae_eq hG hφinv g hf
  have hPR : ∀ g x, V.starProjection (R g x) = R g (V.starProjection x) :=
    fun g x => starProjection_canonicalL2RightAction hG V hV g x
  -- right invariance under `L`
  have hψL : ∀ b ∈ L, ∀ g : AdelicGroupPoints F G, ψ (g * ofFinite F G b) = ψ g := by
    intro b hb
    have hRfb : R (ofFinite F G b) f = f := by
      apply Lp.ext
      refine (hRf _).trans (Filter.EventuallyEq.trans ?_ hf.symm)
      exact Filter.Eventually.of_forall fun y => hφL b hb y.out
    have hRwb : R (ofFinite F G b) w = w := by
      rw [hw_def, ← hPR, hRfb]
    have hae : (fun y : CanonicalQuotient F G => ψ (y.out * ofFinite F G b)) =ᵐ[canonicalMeasure F G]
        fun y => ψ y.out := by
      refine (hRw _).symm.trans ?_
      rw [hRwb]
      exact hψrep
    have heq := eq_of_ae_eq_out hG (u₁ := fun x => ψ (x * ofFinite F G b)) (u₂ := ψ)
      (hψs.1.comp (continuous_id.mul continuous_const)) hψs.1
      (fun c hc x => by
        rw [mul_assoc]
        exact hψinv c hc _) hψinv hae
    exact fun g => congrFun heq g
  -- the functions `k ↦ ψ(g k)` lie in `E`
  have hEU : ∀ i : Unit, FiniteDimensional ℂ ((fun _ : Unit => E) i) := fun _ => hE
  obtain ⟨m, nodes, weights, hwE, hinterp⟩ :=
    Langlands.Analysis.finiteSubspaceInterpolation (K.comap (ofInfinite F G).toMonoidHom) Unit (fun _ => E)
  have hinterpE : ∀ u ∈ E, ∀ k, u k = ∑ j, weights () j k * u (nodes j) := by
    intro u hu k
    have h := hinterp u (le_iSup (fun _ : Unit => E) () hu) k
    simpa using h
  have hrel : ∀ (k : K.comap (ofInfinite F G).toMonoidHom) (x : AdelicGroupPoints F G), ψ (x * ofInfinite F G k) =
      ∑ j, weights () j k * ψ (x * ofInfinite F G (nodes j)) := by
    intro k
    have hRfk : R (ofInfinite F G k) f =
        ∑ j, weights () j k • R (ofInfinite F G (nodes j)) f := by
      apply Lp.ext
      have hall : ∀ᵐ y ∂(canonicalMeasure F G), ∀ j,
          ((weights () j k • R (ofInfinite F G (nodes j)) f : Lp ℂ 2 (canonicalMeasure F G)) :
            CanonicalQuotient F G → ℂ) y =
            weights () j k * φ (y.out * ofInfinite F G (nodes j)) := by
        rw [ae_all_iff]
        intro j
        filter_upwards [Lp.coeFn_smul (weights () j k) (R (ofInfinite F G (nodes j)) f),
          hRf (ofInfinite F G (nodes j))] with y h1 h2
        rw [h1, Pi.smul_apply, h2, smul_eq_mul]
      have hsum : (⇑(∑ j, weights () j k • R (ofInfinite F G (nodes j)) f :
          Lp ℂ 2 (canonicalMeasure F G))) =ᵐ[canonicalMeasure F G]
          fun y => ∑ j, weights () j k * φ (y.out * ofInfinite F G (nodes j)) := by
        filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
          (fun j => weights () j k • R (ofInfinite F G (nodes j)) f), hall] with y h1 h2
        rw [h1]
        exact Finset.sum_congr rfl fun j _ => h2 j
      refine (hRf _).trans (Filter.EventuallyEq.trans ?_ hsum.symm)
      refine Filter.Eventually.of_forall fun y => ?_
      exact hinterpE (fun k' => φ (y.out * ofInfinite F G k')) (hφE y.out) k
    have hRwk : R (ofInfinite F G k) w =
        ∑ j, weights () j k • R (ofInfinite F G (nodes j)) w := by
      rw [hw_def, ← hPR, hRfk, map_sum]
      simp only [map_smul, hPR]
    have hall : ∀ᵐ y ∂(canonicalMeasure F G), ∀ j,
        ((weights () j k • R (ofInfinite F G (nodes j)) w : Lp ℂ 2 (canonicalMeasure F G)) :
          CanonicalQuotient F G → ℂ) y =
          weights () j k * ψ (y.out * ofInfinite F G (nodes j)) := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (weights () j k) (R (ofInfinite F G (nodes j)) w),
        hRw (ofInfinite F G (nodes j))] with y h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hae : (fun y : CanonicalQuotient F G => ψ (y.out * ofInfinite F G k))
        =ᵐ[canonicalMeasure F G]
        fun y => ∑ j, weights () j k * ψ (y.out * ofInfinite F G (nodes j)) := by
      refine (hRw _).symm.trans ?_
      rw [hRwk]
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun j => weights () j k • R (ofInfinite F G (nodes j)) w), hall] with y h1 h2
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => h2 j
    have heq := eq_of_ae_eq_out hG (u₁ := fun x => ψ (x * ofInfinite F G k))
      (u₂ := fun x => ∑ j, weights () j k * ψ (x * ofInfinite F G (nodes j)))
      (hψs.1.comp (continuous_id.mul continuous_const))
      (continuous_finsetSum _ fun j _ =>
        continuous_const.mul (hψs.1.comp (continuous_id.mul continuous_const)))
      (fun c hc x => by
        rw [mul_assoc]
        exact hψinv c hc _)
      (fun c hc x => by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, hψinv c hc])
      hae
    exact fun x => congrFun heq x
  have hψE : ∀ g : AdelicGroupPoints F G, (fun k : K.comap (ofInfinite F G).toMonoidHom => ψ (g * ofInfinite F G k)) ∈ E := by
    intro g
    have heq : (fun k : K.comap (ofInfinite F G).toMonoidHom => ψ (g * ofInfinite F G k)) =
        ∑ j, ψ (g * ofInfinite F G (nodes j)) • weights () j := by
      funext k
      rw [hrel k g, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [heq]
    exact E.sum_mem fun j _ => E.smul_mem _ (hwE () j)
  -- annihilation by `J`
  have hψJ : ∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ h : functionInfiniteSlice F G ψ b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G ψ b, h⟩ = 0 := by
    intro z hz b h
    obtain ⟨k, hk, -, hkeq⟩ := AdelicGroupPoints.adelicRightConvolutionEnveloping hsmooth hcalc
      (z : AdelicEnvelopingAlgebra F G hsmooth) β hβ
    have hφm : Measurable φ := hφs.1.measurable
    have hφi : LocallyIntegrable φ (Measure.haar : Measure (AdelicGroupPoints F G)) :=
      hφs.1.locallyIntegrable
    have hkφ : rightConvolution F G k φ = 0 := by
      funext x
      have h1 := hkeq φ hφm hφi (finite F G x)
      have h2 : AdelicGroupPoints.rightConvolutionSmoothSlice hsmooth β φ hβ hφm hφi (finite F G x) =
          ⟨functionInfiniteSlice F G φ (finite F G x), hφs.2.1 _⟩ := by
        apply Subtype.ext
        funext a
        change rightConvolution F G β φ (pair F G a (finite F G x)) =
          φ (pair F G a (finite F G x))
        rw [hβφ]
      rw [h2] at h1
      have h3 := hφJ z hz (finite F G x) (hφs.2.1 _)
      change plotSmoothEnvelopingAction F G hsmooth hcalc (z : AdelicEnvelopingAlgebra F G hsmooth)
        _ = 0 at h3
      rw [h3] at h1
      have h4 := congrArg (fun v : InfinitePlotSmoothFunctions F G => v.val (infinite F G x)) h1
      change (0 : ℂ) = rightConvolution F G k φ (pair F G (infinite F G x) (finite F G x)) at h4
      rw [pair_projections] at h4
      exact h4.symm
    have hki : Integrable k (Measure.haar : Measure (AdelicGroupPoints F G)) :=
      hk.1.1.integrable_of_hasCompactSupport hk.2.1
    have hRkf : canonicalL2IntegratedAction hG k hki f = 0 := by
      apply Lp.ext
      refine (hint_f k hki).trans ?_
      filter_upwards [Lp.coeFn_zero ℂ 2 (canonicalMeasure F G)] with y hy
      rw [hy, hkφ]
      rfl
    have hRkw : canonicalL2IntegratedAction hG k hki w = 0 := by
      rw [hw_def, ← starProjection_canonicalL2IntegratedAction hG V hV, hRkf, map_zero]
    have hsm0 : canonicalL2Smoothing k w = 0 := by
      have hae := canonicalL2IntegratedAction_ae_eq hG k hki w
      rw [hRkw] at hae
      refine eq_of_ae_eq_out hG (isAdelicSmoothFunction_canonicalL2Smoothing hG hsmooth hk w).1
        continuous_const (fun c hc x => canonicalL2Smoothing_mul k w c hc x)
        (fun c hc x => rfl) ?_
      refine hae.symm.trans ?_
      filter_upwards [Lp.coeFn_zero ℂ 2 (canonicalMeasure F G)] with y hy
      rw [hy]
      rfl
    have h1 := hkeq (canonicalL2Pullback w) (measurable_canonicalL2Pullback w)
      (locallyIntegrable_canonicalL2Pullback hG w) b
    have h2 : (⟨functionInfiniteSlice F G ψ b, h⟩ : InfinitePlotSmoothFunctions F G) =
        AdelicGroupPoints.rightConvolutionSmoothSlice hsmooth β (canonicalL2Pullback w) hβ
          (measurable_canonicalL2Pullback w) (locallyIntegrable_canonicalL2Pullback hG w) b :=
      Subtype.ext rfl
    have key : plotSmoothCenterAction F G hsmooth hcalc z
        (AdelicGroupPoints.rightConvolutionSmoothSlice hsmooth β (canonicalL2Pullback w) hβ
          (measurable_canonicalL2Pullback w) (locallyIntegrable_canonicalL2Pullback hG w) b) = 0 := by
      change plotSmoothEnvelopingAction F G hsmooth hcalc (z : AdelicEnvelopingAlgebra F G hsmooth)
        _ = 0
      rw [h1]
      apply Subtype.ext
      funext a
      change canonicalL2Smoothing k w (pair F G a b) = 0
      rw [hsm0]
      rfl
    exact (congrArg (plotSmoothCenterAction F G hsmooth hcalc z) h2).trans key
  -- moderate growth
  have hψgrowth : HasModerateGrowthFunction F G rho ψ :=
    hasModerateGrowthFunction_canonicalL2Smoothing hG rho hrho ⟨⟨β, hβ.1.1⟩, hβ.2.1⟩ w
  refine ⟨ψ, ⟨fun c hc x => hψinv c (principal_le_rationalSubgroup F G _ _ hc) x, hψs,
    isInfiniteSubgroupFiniteFunction_of_mem hψE, ⟨J, hJ, hψJ⟩, hψgrowth⟩,
    fun c hc x => hψinv c (subgroup_le_rationalSubgroup F G _ _ hc) x, hψL, hψJ, hψE, hψrep⟩

end Langlands.Global
