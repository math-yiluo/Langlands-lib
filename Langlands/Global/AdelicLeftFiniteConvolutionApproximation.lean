import Langlands.Global.AdelicWavePacketTranslationReduction
import Langlands.Global.AdelicRationalQuotientL2RightAction
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Approximation of a right translate by left-finite convolutions -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local notation "Ad" => AdelicGroupPoints F G
local notation "Q" => RationalQuotient F G
local notation "Γ" => rationalSubgroup F G
local notation "μQ" => rationalQuotientHaarMeasure F G
local notation "L²" => Lp ℂ 2 μQ

private def leftOrbit (k : InfiniteAdelicGroupPoints F G) : (Ad → ℂ) →ₗ[ℂ] (Ad → ℂ) where
  toFun a g := a (ofInfinite F G k * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def orbitSpan (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (a : Ad → ℂ) :
    Submodule ℂ (Ad → ℂ) := Submodule.span ℂ (Set.range fun k : Kinf => leftOrbit k.val a)

omit [IsAffineHom G.X.hom] in
/-- The left-finite test functions are a complex submodule with pointwise operations. -/
def leftFiniteTestFunctions (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) :
    Submodule ℂ (Ad → ℂ) where
  carrier := {a | IsLeftFiniteTestFunction F G Kinf a}
  zero_mem' := by
    refine ⟨continuous_const, HasCompactSupport.zero, ?_, ⊤, isOpen_univ, fun _ _ _ => rfl⟩
    have hspan : orbitSpan Kinf (0 : Ad → ℂ) = ⊥ := by
      apply bot_unique
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact (⊥ : Submodule ℂ (Ad → ℂ)).zero_mem
    change FiniteDimensional ℂ (orbitSpan Kinf (0 : Ad → ℂ))
    rw [hspan]
    infer_instance
  add_mem' {a b} ha hb := by
    rcases ha with ⟨hac, has, haf, A, hAo, hA⟩
    rcases hb with ⟨hbc, hbs, hbf, B, hBo, hB⟩
    refine ⟨hac.add hbc, has.add hbs, ?_, A ⊓ B, hAo.inter hBo, ?_⟩
    · let : FiniteDimensional ℂ (orbitSpan Kinf a) := haf
      let : FiniteDimensional ℂ (orbitSpan Kinf b) := hbf
      apply Submodule.finiteDimensional_of_le (S₂ := orbitSpan Kinf a ⊔ orbitSpan Kinf b)
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change leftOrbit k.val (a + b) ∈ orbitSpan Kinf a ⊔ orbitSpan Kinf b
      rw [map_add]
      exact (orbitSpan Kinf a ⊔ orbitSpan Kinf b).add_mem
        (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩))
    · intro t ht g
      change t ∈ A ⊓ B at ht
      simp only [Pi.add_apply, hA t ht.1 g, hB t ht.2 g]
  smul_mem' z a ha := by
    rcases ha with ⟨hac, has, haf, A, hAo, hA⟩
    refine ⟨continuous_const.smul hac, has.smul_left, ?_, A, hAo, ?_⟩
    · let : FiniteDimensional ℂ (orbitSpan Kinf a) := haf
      apply Submodule.finiteDimensional_of_le (S₂ := orbitSpan Kinf a)
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change leftOrbit k.val (z • a) ∈ orbitSpan Kinf a
      rw [map_smul]
      exact (orbitSpan Kinf a).smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
    · intro t ht g
      simp only [Pi.smul_apply, hA t ht g]

variable (K : Subgroup (AdelicGroupPoints F G))

local notation "Test" => leftFiniteTestFunctions (Subgroup.comap
  (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K)

variable {Θ : AdelicGroupPoints F G → ℂ} (hΘc : Continuous Θ)

omit [IsAffineHom G.X.hom] in
include hΘc in
private theorem convolution_integrable {a : Ad → ℂ} (ha : Continuous a) (has : HasCompactSupport a)
    (g : Ad) : Integrable (fun h => a h * Θ (g * h)) Measure.haar :=
  (ha.mul (hΘc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport has.mul_right

omit [IsAffineHom G.X.hom] in
include K hΘc in
set_option maxHeartbeats 800000 in
private def convolutionToL2
    (hconv : ∀ a : Test, MemLp (fun z : Q => rightConvolution F G a.val Θ z.out) 2 μQ) :
    Test →ₗ[ℂ] L² := by
  let f (a : Test) : L² := (hconv a).toLp (fun z => rightConvolution F G a.val Θ z.out)
  have hf (a : Test) : ⇑(f a) =ᵐ[μQ] fun z : Q => rightConvolution F G a.val Θ z.out :=
    (hconv a).coeFn_toLp
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro a b
    apply Lp.ext
    filter_upwards [hf (a + b), Lp.coeFn_add (f a) (f b), hf a, hf b] with z hab hz ha hb
    rw [hab, hz, Pi.add_apply, ha, hb]
    simp only [rightConvolution, Submodule.coe_add, Pi.add_apply, add_mul]
    have hta : IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) a.val := a.property
    have htb : IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) b.val := b.property
    exact integral_add (convolution_integrable hΘc hta.1 hta.2.1 z.out)
      (convolution_integrable hΘc htb.1 htb.2.1 z.out)
  · intro c a
    apply Lp.ext
    filter_upwards [hf (c • a), Lp.coeFn_smul c (f a), hf a] with z hca hz ha
    rw [hca, RingHom.id_apply, hz, Pi.smul_apply, ha]
    simp only [rightConvolution, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul]

omit [IsAffineHom G.X.hom] in
private theorem rightAction_rep (hG : IsConnectedReductive G) (y : Ad) {f : L²} {r : Q → ℂ}
    (hrep : ⇑f =ᵐ[μQ] r) :
    ⇑(rationalQuotientL2RightAction hG y f) =ᵐ[μQ]
      fun z => r (LeftCosetSpace.rightTranslate Γ y z) := by
  let := adelicHaarUnimodularity.2 F G hG
  have hp := measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G y
  refine (coeFn_rationalQuotientL2RightAction hG y f).trans ?_
  filter_upwards [hp.quasiMeasurePreserving.ae_eq_comp hrep] with z hz
  have hzout : LeftCosetSpace.mk Γ z.out = z := Quotient.out_eq z
  rw [← LeftCosetSpace.rightTranslate_mk, hzout]
  exact hz

include K hΘc in
set_option maxHeartbeats 800000 in
/-- Right-translation test-function separation implies norm approximation by a single convolution
for a continuous left invariant `L²` function with square-integrable left-finite convolutions. -/
theorem exists_leftFinite_convolution_approximation
    (hSep : RightTranslationTestFunctionSeparationStatement)
    (hG : IsConnectedReductive G) (hK : IsMaximalCompactSubgroup F G K)
    (hΘinv : IsLeftInvariantUnder F G Γ Θ) (hΘ : MemLp (fun z : Q => Θ z.out) 2 μQ)
    (hconv : ∀ a : Test, MemLp (fun z : Q => rightConvolution F G a.val Θ z.out) 2 μQ)
    (y : Ad) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Test, eLpNorm (fun z : Q => Θ (z.out * y) - rightConvolution F G a.val Θ z.out)
      2 μQ < ENNReal.ofReal ε := by
  let S := convolutionToL2 K hΘc hconv
  let R := rationalQuotientL2RightAction hG
  let θ := hΘ.toLp _
  have hinv : ∀ f : L², R y (R y⁻¹ f) = f := by
    intro f
    change (R y * R y⁻¹) f = f
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have horth : R y θ ∈ S.rangeᗮᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro f hf
    have hpair (a : Test) : ∫ z : Q, f z * conj (rightConvolution F G a.val Θ z.out) ∂μQ = 0 := by
      rw [← (Submodule.mem_orthogonal _ _).mp hf (S a) ⟨a, rfl⟩, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hconv a).coeFn_toLp] with z hz
      have hza : (S a) z = rightConvolution F G a.val Θ z.out := hz
      rw [hza, RCLike.inner_apply', mul_comm]
    have hshift := hSep F G hG K hK f (Lp.memLp f) Θ hΘinv hΘ
      (fun a ha => hpair ⟨a, ha⟩) y⁻¹
    let I : L² →ₗᵢ[ℂ] L² := ⟨(R y).toLinearMap, norm_rationalQuotientL2RightAction hG y⟩
    calc
      inner ℂ (R y θ) f = inner ℂ (I θ) (I (R y⁻¹ f)) := by
        change inner ℂ (R y θ) f = inner ℂ (R y θ) (R y (R y⁻¹ f))
        rw [hinv]
      _ = inner ℂ θ (R y⁻¹ f) := I.inner_map_map _ _
      _ = 0 := by
        rw [← hshift, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hΘ.coeFn_toLp, rightAction_rep hG y⁻¹ (f := f) (r := ⇑f) (Filter.EventuallyEq.rfl)] with z hz hz'
        change inner ℂ (θ z) ((R y⁻¹ f) z) = _
        rw [hz, hz', RCLike.inner_apply', mul_comm]
  rw [Submodule.orthogonal_orthogonal_eq_closure] at horth
  have hm : R y θ ∈ closure (S.range : Set L²) := horth
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hm ε hε
  refine ⟨a, ?_⟩
  have hnorm : eLpNorm (fun z : Q => Θ (z.out * y) - rightConvolution F G a.val Θ z.out) 2 μQ =
      ‖R y θ - S a‖ₑ := by
    rw [Lp.enorm_def]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (R y θ) (S a), rightAction_rep hG y hΘ.coeFn_toLp,
      (hconv a).coeFn_toLp] with z hsub hz hz'
    change (R y θ) z = Θ ((LeftCosetSpace.rightTranslate Γ y z).out) at hz
    rw [hsub, Pi.sub_apply, hz]
    change _ = _ - ((hconv a).toLp _) z
    have hr : LeftCosetSpace.rightTranslate Γ y z = LeftCosetSpace.mk Γ (z.out * y) := by
      rw [← LeftCosetSpace.rightTranslate_mk, show LeftCosetSpace.mk Γ z.out = z from Quotient.out_eq z]
    rw [hz', hr]
    exact congrArg (fun c : ℂ => c - _) (LeftCosetSpace.out_mk_of_invariant Γ Θ hΘinv _).symm
  rw [hnorm, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by simpa only [dist_eq_norm, norm_sub_rev] using ha)

end Langlands.Global

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The separation property implies approximation of a single right translate by the
left-finite convolutions of the original function. -/
def LeftFiniteConvolutionApproximationStatement : Prop :=
  RightTranslationTestFunctionSeparationStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G → ∀ (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
    ∀ (Θ : AdelicGroupPoints F G → ℂ), Continuous Θ →
      IsLeftInvariantUnder F G (rationalSubgroup F G) Θ →
      MemLp (fun z : RationalQuotient F G => Θ z.out) 2 (rationalQuotientHaarMeasure F G) →
    let Test := IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom)
    (∀ a, Test a → MemLp (fun z : RationalQuotient F G => rightConvolution F G a Θ z.out) 2
      (rationalQuotientHaarMeasure F G)) →
    ∀ (y : AdelicGroupPoints F G) (ε : ℝ), 0 < ε → ∃ a, Test a ∧
      eLpNorm (fun z : RationalQuotient F G => Θ (z.out * y) - rightConvolution F G a Θ z.out)
        2 (rationalQuotientHaarMeasure F G) < ENNReal.ofReal ε

theorem leftFiniteConvolutionApproximation : LeftFiniteConvolutionApproximationStatement := by
  intro hSep F _ _ G _ _ _ hG K hK Θ hΘc hΘinv hΘ Test hconv y ε hε
  obtain ⟨a, ha⟩ := exists_leftFinite_convolution_approximation K hΘc hSep hG hK hΘinv hΘ
    (fun a => hconv a.val a.property) y ε hε
  exact ⟨a.val, a.property, ha⟩

end Langlands.Global
