import Langlands.Analysis.Meromorphic.WeakHolomorphy
import Langlands.Analysis.SeveralComplex.JointQuotientContinuity
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Joint evaluation of families of uniform moderate growth -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Set
open scoped CategoryTheory.MonObj ENNReal NNReal Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

section

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- Apply the operator-norm weak holomorphy criterion with one-dimensional source. -/
private theorem continuousOn_of_weak {T : Set E} {f : E → B} (hT : IsOpen T)
    (hf : ∀ φ : StrongDual ℂ B, DifferentiableOn ℂ (fun s => φ (f s)) T) :
    ContinuousOn f T := by
  let g : E → ℂ →L[ℂ] B := fun s => ContinuousLinearMap.toSpanSingleton ℂ (f s)
  have hg : ∀ v (φ : StrongDual ℂ B), DifferentiableOn ℂ (fun s => φ (g s v)) T := by
    intro v φ
    simpa only [g, ContinuousLinearMap.toSpanSingleton_apply, map_smul, smul_eq_mul]
      using (hf φ).const_mul v
  intro s hs
  have hc := Langlands.Analysis.Meromorphic.WeakHolomorphy.continuousAt_of_weak hT hg hs
  simpa only [g, ContinuousLinearMap.toSpanSingleton_apply_one] using
    (hc.clm_apply (continuousAt_const (y := (1 : ℂ)))).continuousWithinAt

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "Gad" => AdelicGroupPoints F G
local notation "V" => lp (fun _ : Gad => ℂ) ∞
local notation "D" => weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L

/-- A weakly holomorphic family is continuous for the topology of weighted derivatives. -/
theorem UniformGrowthFrechetSpace.continuousOn_of_differentiableOn_dual {T : Set E} {a : E → 𝔉}
    (hT : IsOpen T) (ha : ∀ φ : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => φ (a s)) T) :
    ContinuousOn a T := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous[_, ⨅ b : AdelicEnvelopingAlgebra F G hsmooth,
    TopologicalSpace.induced (D b) inferInstance] _
  refine continuous_iInf_rng.mpr fun b => continuous_induced_rng.mpr ?_
  exact continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_of_weak hT (fun φ => ha (φ.comp (D b))))

omit [IsAffine G.X.left] in
include hN in
private theorem continuous_growthWeight :
    Continuous (fun g : Gad => RepresentationGrowth.adelicSourceNorm F G rho g ^ R) := by
  let C : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hC : C ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  have hc : Continuous (RepresentationGrowth.adelicSourceNorm F G rho) := by
    convert (RepresentationGrowth.continuous_adelicHeight F G rho hN).div_const C using 1
    funext g
    have hg : RepresentationGrowth.adelicHeight F G rho g =
        C * RepresentationGrowth.adelicSourceNorm F G rho g :=
      RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g
    rw [hg, mul_comm, mul_div_cancel_right₀ _ hC]
  exact hc.rpow_const fun g => Or.inl (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g).ne'

/-- The underlying evaluation is continuous jointly in the vector and in the actual adelic
point (`𝔉` has its seminorm topology). -/
theorem UniformGrowthFrechetSpace.continuous_uncurry_toFun :
    Continuous (fun p : 𝔉 × Gad => toFun F G rho hsmooth hcalc hN hrho R L p.1 p.2) := by
  let w : Gad → ℂ := fun g => (RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ)
  have hw : Continuous w := Complex.continuous_ofReal.comp (continuous_growthWeight F G rho hN R)
  let C := {b : V // Continuous (fun g : Gad => b g)}
  have hb (f : 𝔉) : Continuous (fun g : Gad => D 1 f g) := by
    have hf : Continuous (toFun F G rho hsmooth hcalc hN hrho R L f) := by
      let f₀ := (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val
      exact f₀.property
    simp only [weightedDerivativeCLM_apply, weightedDerivative_one_apply]
    exact hf.mul (hw.inv₀ fun g => Complex.ofReal_ne_zero.mpr
      ((Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R).ne'))
  let b : 𝔉 → C := fun f => ⟨D 1 f, hb f⟩
  have hbc : Continuous b := (D 1).continuous.subtype_mk (hb ·)
  have he : Continuous (fun q : C × Gad => (q.1 : V) q.2) := by
    refine continuous_prod_of_continuous_lipschitzWith _ 1 (·.2) (fun g => ?_)
    refine LipschitzWith.of_dist_le_mul fun f f' => ?_
    change dist ((f : V) g) ((f' : V) g) ≤ (↑(1 : ℝ≥0)) * dist (f : V) (f' : V)
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul, lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero ((f : V) - (f' : V)) g
  have hc := (he.comp ((hbc.comp continuous_fst).prodMk continuous_snd)).mul
    (hw.comp continuous_snd)
  refine hc.congr ?_
  rintro ⟨f, g⟩
  have hne : w g ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R).ne'
  change D 1 f g * w g = _
  rw [weightedDerivativeCLM_apply, weightedDerivative_one_apply]
  exact inv_mul_cancel_right₀ hne _

/-- Clear a nontrivial scalar factor in a pointwise holomorphic family once the product is a
continuous scalar multiple of a weakly holomorphic uniform-growth numerator. -/
theorem UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval {T : Set E} {a : E → 𝔉}
    {q p : E → ℂ} {h : E → Gad → ℂ} (hT : IsOpen T) (hTc : IsPreconnected T)
    (hq : DifferentiableOn ℂ q T) (hqne : ∃ s ∈ T, q s ≠ 0) (hp : ContinuousOn p T)
    (ha : ∀ φ : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => φ (a s)) T)
    (hh : ∀ g, DifferentiableOn ℂ (fun s => h s g) T)
    (heq : ∀ s ∈ T, ∀ g, q s * h s g = p s * toFun F G rho hsmooth hcalc hN hrho R L (a s) g) :
    ContinuousOn (fun r : E × Gad => h r.1 r.2) (T ×ˢ univ) := by
  have hac := continuousOn_of_differentiableOn_dual F G rho hsmooth hcalc hN hrho R L hT ha
  have hfst : MapsTo (Prod.fst : E × Gad → E) (T ×ˢ univ) T := fun _ hx => hx.1
  have he := (continuous_uncurry_toFun F G rho hsmooth hcalc hN hrho R L).comp_continuousOn
    ((hac.comp continuous_fst.continuousOn hfst).prodMk continuous_snd.continuousOn)
  exact Langlands.Analysis.SeveralComplex.continuousOn_of_differentiableOn_of_mul hT hTc hq hqne hh
    (((hp.comp continuous_fst.continuousOn hfst).mul he).congr fun r hr => heq r.1 hr.1 r.2)

end

/-- Joint continuity of a scalar holomorphic family whose product with a local denominator
comes from weakly holomorphic uniform-growth data in complex coordinates. -/
def UniformGrowthJointContinuityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (N d : ℕ) (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho) (R : ℝ)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (n : ℕ),
    let E := Fin n → ℂ
    let 𝔉 := UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
    let Gad := AdelicGroupPoints F G
    ∀ (T : Set E) (a : E → 𝔉) (q p : E → ℂ) (h : E → Gad → ℂ),
      IsOpen T → IsPreconnected T → DifferentiableOn ℂ q T → (∃ s ∈ T, q s ≠ 0) → ContinuousOn p T →
      (∀ φ : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => φ (a s)) T) →
      (∀ g, DifferentiableOn ℂ (fun s => h s g) T) →
      (∀ s ∈ T, ∀ g, q s * h s g =
        p s * UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (a s) g) →
      ContinuousOn (fun r : E × Gad => h r.1 r.2) (T ×ˢ univ)

theorem uniformGrowthJointContinuity : UniformGrowthJointContinuityStatement.{u} := by
  intro F _ _ G _ N d rho hsmooth hcalc hN hrho R L n
  dsimp only
  intro T a q p h hT hTc hq hqne hp ha hh heq
  exact UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval F G rho hsmooth hcalc hN hrho R L
    hT hTc hq hqne hp ha hh heq

end Langlands.Automorphic.GroupSchemeFunctions
