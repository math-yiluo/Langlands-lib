import Langlands.Global.AdelicNormOneKernelVector
import Langlands.Global.AdelicRadicalKernelCovariance
import Langlands.Global.AdelicParabolicConstantTermAutomorphy

/-! # Smoothing a family of norm-one Levi classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise Topology NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "ι" => map F M G (fam.l J ≫ fam.p J)
local notation "ιU" => map F (fam.U J) G (fam.iU J ≫ fam.p J)
local notation "Q" => PositiveRationalQuotient F M T i
local notation "V" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F M T i)
local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "πP" => positiveFactor F M T i hi I e
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "δ" => fam.leviModulus J

/-- The conjugated radical kernel at the inverse Levi argument, translated by a positive point. -/
def leviFibreSmoothingKernel (β : C_c(A, ℂ)) (g : A) (b : Pos) : C_c(AM, ℂ) := by
  let L := fam.radicalKernelCc J β g 1
  let E := (Homeomorph.inv AM).trans (Homeomorph.mulLeft (pp b))
  exact ⟨⟨fun z => starRingEnd ℂ (L (E z)), continuous_star.comp (L.continuous.comp E.continuous)⟩,
    (L.hasCompactSupport.comp_homeomorph E).comp_left (map_zero _)⟩

omit [(characterRestrict i).range.FiniteIndex] in
@[simp] theorem leviFibreSmoothingKernel_apply (β : C_c(A, ℂ)) (g : A) (b : Pos) (z : AM) :
    fam.leviFibreSmoothingKernel J T i β g b z =
      starRingEnd ℂ (fam.radicalKernel J β g 1 (pp b * z⁻¹)) := rfl

/-- The weighted evaluation of a norm-one class by the reflected radical kernel. -/
def leviFibreSmoothingIntegrand (β : C_c(A, ℂ)) (g : A) (b : Pos) (x : A₁) (v : V) : ℂ :=
  (δ (pp b) : ℝ)⁻¹ •
    normOnePartialConvolution T i (fam.leviFibreSmoothingKernel J T i β g b) (v : Q → ℂ) (x : AM)

/-- A family of norm-one classes gives a function on the ambient group by integrating the
weighted evaluations over the positive subgroup. -/
def leviFibreSmoothing (β : C_c(A, ℂ)) (w : Pos → V) (g : A) : ℂ :=
  ∫ b, fam.leviFibreSmoothingIntegrand J T i β g b 1 (w b) ∂νP

include hi e in
/-- With the ambient parameter in a compact set there is a common compact positive support,
independently of the norm-one point and the class. -/
theorem exists_compact_support_leviFibreSmoothingIntegrand (β : C_c(A, ℂ))
    {C : Set A} (hC : IsCompact C) :
    ∃ D : Set Pos, IsCompact D ∧ ∀ g ∈ C, ∀ b ∉ D, ∀ (x : A₁) (v : V),
      fam.leviFibreSmoothingIntegrand J T i β g b x v = 0 := by
  obtain ⟨E, hE, hSupp⟩ := fam.exists_compact_tsupport_radicalKernelCc J β hC
    (isCompact_singleton (x := (1 : A)))
  refine ⟨πP '' E, hE.image (πP).continuous, fun g hg b hb x v => ?_⟩
  unfold leviFibreSmoothingIntegrand normOnePartialConvolution
  have hzero (n : A₁) : fam.radicalKernel J β g 1 (pp b * (((n : AM)⁻¹ * (x : AM))⁻¹)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fam.radicalKernelCc J β g 1)
    intro hn
    apply hb
    refine ⟨_, hSupp g hg 1 rfl hn, ?_⟩
    rw [map_mul, map_inv, map_mul, map_inv, positiveFactor_positivePointMap,
      positiveFactor_normOne, positiveFactor_normOne, inv_one, one_mul, inv_one, mul_one]
  simp only [leviFibreSmoothingKernel_apply, hzero, map_zero, zero_mul, integral_zero, smul_zero]

variable [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

include hi e hc in
/-- If the classes depend continuously on the positive point, the weighted evaluations are
jointly continuous in the ambient, positive and norm-one points. -/
theorem continuous_leviFibreSmoothingIntegrand (β : C_c(A, ℂ)) (w : Pos → V)
    (hw : Continuous w) :
    Continuous fun p : A × Pos × A₁ => fam.leviFibreSmoothingIntegrand J T i β p.1 p.2.1 p.2.2
      (w p.2.1) := by
  let := positiveLocallyCompactSpace F T I e
  let K : A × Pos × A₁ → C_c(AM, ℂ) := fun p =>
    rightTranslateCc (fam.leviFibreSmoothingKernel J T i β p.1 p.2.1) p.2.2
  have hg : Continuous (fun p : (A × Pos × A₁) × AM => p.1.1) :=
    continuous_fst.comp continuous_fst
  have hb : Continuous (fun p : (A × Pos × A₁) × AM => pp p.1.2.1) :=
    (pp).continuous.comp (continuous_fst.comp (continuous_snd.comp continuous_fst))
  have hx : Continuous (fun p : (A × Pos × A₁) × AM => (p.1.2.2 : AM)) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hm : Continuous (fun p : (A × Pos × A₁) × AM => pp p.1.2.1 * (p.2 * (p.1.2.2 : AM))⁻¹) :=
    hb.mul (continuous_snd.mul hx).inv
  have hK : Continuous fun p : (A × Pos × A₁) × AM => K p.1 p.2 := by
    let f : (A × Pos × A₁) × AM → A × A × AM := fun p =>
      (p.1.1, 1, pp p.1.2.1 * (p.2 * (p.1.2.2 : AM))⁻¹)
    have hf : Continuous f := hg.prodMk (continuous_const.prodMk hm)
    have hL : Continuous (fun p : (A × Pos × A₁) × AM =>
        fam.radicalKernel J β (f p).1 (f p).2.1 (f p).2.2) :=
      (fam.continuous_radicalKernel J β).comp' hf
    change Continuous (fun p : (A × Pos × A₁) × AM =>
      star (fam.radicalKernel J β (f p).1 (f p).2.1 (f p).2.2))
    exact hL.star
  have hS (p₀ : A × Pos × A₁) : ∃ U ∈ nhds p₀, ∃ E : Set AM, IsCompact E ∧
      ∀ p ∈ U, tsupport (K p) ⊆ E := by
    obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds p₀.1
    obtain ⟨D, hD, hDb⟩ := exists_compact_mem_nhds p₀.2.1
    obtain ⟨U, hU, hUx⟩ := exists_compact_mem_nhds p₀.2.2
    obtain ⟨E, hE, hSupp⟩ := fam.exists_compact_tsupport_radicalKernelCc J β hC
      (isCompact_singleton (x := (1 : A)))
    have hP := hD.image (pp).continuous
    have hA := hU.image (continuous_subtype_val : Continuous ((↑) : A₁ → AM))
    have hF : IsCompact (E⁻¹ * (pp '' D) * ((↑) '' U : Set AM)⁻¹) :=
      (hE.inv.mul hP).mul hA.inv
    refine ⟨C ×ˢ D ×ˢ U, prod_mem_nhds hCg (prod_mem_nhds hDb hUx), _, hF, fun p hp => ?_⟩
    refine closure_minimal (fun z hz => ?_) hF.isClosed
    let m : AM := pp p.2.1 * (z * (p.2.2 : AM))⁻¹
    have hm : fam.radicalKernelCc J β p.1 1 m ≠ 0 := by
      intro hm
      apply hz
      change starRingEnd ℂ (fam.radicalKernelCc J β p.1 1 m) = 0
      rw [hm, map_zero]
    refine ⟨m⁻¹ * pp p.2.1, ⟨m⁻¹, Set.inv_mem_inv.mpr (hSupp p.1 hp.1 1 rfl
      (subset_tsupport _ hm)), pp p.2.1, ⟨p.2.1, hp.2.1, rfl⟩, rfl⟩,
      (p.2.2 : AM)⁻¹, Set.inv_mem_inv.mpr ⟨p.2.2, hp.2.2, rfl⟩, ?_⟩
    dsimp [m]
    group
  have hv := continuous_normOneKernelVector_comp T i hi I e hc K hK hS
  have hδ : Continuous fun b : Pos => (δ (pp b) : ℝ)⁻¹ :=
    (NNReal.continuous_coe.comp ((fam.continuous_leviModulus J).comp (pp).continuous)).inv₀
      fun b => (NNReal.coe_pos.mpr (fam.leviModulus_pos J (pp b))).ne'
  have hh : Continuous fun p : A × Pos × A₁ => inner ℂ (normOneKernelVector T i hi I e hc (K p))
      (w p.2.1) := hv.inner (hw.comp (continuous_fst.comp continuous_snd))
  have hp := (hδ.comp (continuous_fst.comp continuous_snd)).smul hh
  refine hp.congr fun p => ?_
  change (δ (pp p.2.1) : ℝ)⁻¹ • inner ℂ (normOneKernelVector T i hi I e hc (K p)) (w p.2.1) = _
  exact congrArg ((δ (pp p.2.1) : ℝ)⁻¹ • ·)
    (normOnePartialConvolution_eq_inner T i hi I e hc _ (w p.2.1) (p.2.2 : AM)).symm

include hi e hc in
/-- The positive-point integral converges for each ambient and norm-one point. -/
theorem integrable_leviFibreSmoothingIntegrand (β : C_c(A, ℂ)) (w : Pos → V) (hw : Continuous w)
    (g : A) (x : A₁) :
    Integrable (fun b => fam.leviFibreSmoothingIntegrand J T i β g b x (w b)) νP := by
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  let : T2Space Pos := (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  have hcont := (fam.continuous_leviFibreSmoothingIntegrand J T i hi I e hc β w hw).comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const) :
      Continuous (fun b : Pos => ((g, b, x) : A × Pos × A₁)))
  obtain ⟨D, hD, hSupp⟩ := fam.exists_compact_support_leviFibreSmoothingIntegrand J T i hi I e β
    (isCompact_singleton (x := g))
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hD fun b hb => hSupp g rfl b hb x (w b))

include hi e hc in
/-- Integrating the smoothed evaluations gives a continuous function on the ambient group. -/
theorem continuous_leviFibreSmoothing (β : C_c(A, ℂ)) (w : Pos → V) (hw : Continuous w) :
    Continuous (fam.leviFibreSmoothing J T i hi I e hc β w) := by
  let := positiveLocallyCompactSpace F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  let : T2Space Pos := (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  have hcont : Continuous fun p : A × Pos =>
      fam.leviFibreSmoothingIntegrand J T i β p.1 p.2 1 (w p.2) :=
    Continuous.comp' (g := fun p : A × Pos × A₁ =>
      fam.leviFibreSmoothingIntegrand J T i β p.1 p.2.1 p.2.2 (w p.2.1))
      (f := fun p : A × Pos => ((p.1, p.2, 1) : A × Pos × A₁))
      (fam.continuous_leviFibreSmoothingIntegrand J T i hi I e hc β w hw)
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨D, hD, hSupp⟩ := fam.exists_compact_support_leviFibreSmoothingIntegrand J T i hi I e β hC
  have hDcont : Continuous fun g : A =>
      ∫ b in D, fam.leviFibreSmoothingIntegrand J T i β g b 1 (w b) ∂νP :=
    continuous_parametric_integral_of_continuous hcont hD
  refine hDcont.continuousAt.congr ?_
  filter_upwards [hCg] with g hg
  unfold leviFibreSmoothing
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun b hb => hSupp g hg b hb 1 (w b)

omit [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]
  [(characterRestrict i).range.FiniteIndex] in
/-- A left radical translation leaves each weighted evaluation fixed. -/
theorem leviFibreSmoothingIntegrand_mul_radical (β : C_c(A, ℂ)) (g : A)
    (u₀ : AdelicGroupPoints F (fam.U J)) (b : Pos) (x : A₁) (v : V) :
    fam.leviFibreSmoothingIntegrand J T i β (ιU u₀ * g) b x v =
      fam.leviFibreSmoothingIntegrand J T i β g b x v := by
  simp only [leviFibreSmoothingIntegrand, normOnePartialConvolution,
    leviFibreSmoothingKernel_apply, radicalKernel_mul_radical]

omit [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]
  [(characterRestrict i).range.FiniteIndex] in
include hc in
/-- Left multiplication by a Levi element changes the positive variable by its positive part
and the evaluation point by its norm-one part. The modulus of the positive part cancels. -/
theorem leviFibreSmoothingIntegrand_mul_levi (β : C_c(A, ℂ)) (g : A)
    (a b : Pos) (x : A₁) (v : V) :
    fam.leviFibreSmoothingIntegrand J T i β (ι (pp a * (x : AM)) * g) (a * b) 1 v =
      fam.leviFibreSmoothingIntegrand J T i β g b x v := by
  unfold leviFibreSmoothingIntegrand normOnePartialConvolution
  rw [← integral_smul, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun n => ?_)
  have harg : (pp a * (x : AM))⁻¹ * (pp (a * b) * (((n : AM)⁻¹ * (1 : A₁).val)⁻¹)) =
      pp b * (((n : AM)⁻¹ * (x : AM))⁻¹) := by
    have h1 : (1 : A₁).val = (1 : AM) := rfl
    rw [h1, mul_one, inv_inv, map_mul, mul_inv_rev (pp a)]
    calc
      _ = (x : AM)⁻¹ * (pp b * (n : AM)) := by group
      _ = pp b * (((n : AM)⁻¹ * (x : AM))⁻¹) := by
        rw [← mul_assoc, ← (positivePointMap_commute F M T i hc b (x : AM)⁻¹).eq,
          mul_assoc, mul_inv_rev, inv_inv]
  have hmod := fam.leviModulus_eq_one_of_mem_normOne J x.property
  have ha : (δ (pp a) : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (fam.leviModulus_pos J (pp a))).ne'
  have hab : (δ (pp (a * b)) : ℝ) = (δ (pp a) : ℝ) * (δ (pp b) : ℝ) := by
    rw [map_mul, leviModulus_mul, NNReal.coe_mul]
  have hax : (δ (pp a * (x : AM)) : ℝ) = (δ (pp a) : ℝ) := by
    rw [leviModulus_mul, hmod, mul_one]
  simp only [leviFibreSmoothingKernel_apply, Complex.conj_conj]
  rw [radicalKernel_mul_levi, harg, hab, hax, smul_mul_assoc, smul_smul,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ ha, mul_one]

omit [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]
  [(characterRestrict i).range.FiniteIndex] in
include hc in
/-- A left norm-one Levi translation moves the fibre evaluation from `1` to that point. -/
theorem leviFibreSmoothingIntegrand_mul_normOne (β : C_c(A, ℂ)) (g : A)
    (b : Pos) (x : A₁) (v : V) :
    fam.leviFibreSmoothingIntegrand J T i β (ι (x : AM) * g) b 1 v =
      fam.leviFibreSmoothingIntegrand J T i β g b x v := by
  simpa only [map_one, one_mul] using
    fam.leviFibreSmoothingIntegrand_mul_levi J T i hc β g 1 b x v

omit [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant] in
/-- The smoothing on a Levi translate can be recentered in the positive variable. -/
theorem leviFibreSmoothing_mul_levi (β : C_c(A, ℂ)) (w : Pos → V) (g : A) (a : Pos) (x : A₁) :
    fam.leviFibreSmoothing J T i hi I e hc β w (ι (pp a * (x : AM)) * g) =
      ∫ b, fam.leviFibreSmoothingIntegrand J T i β g b x (w (a * b)) ∂νP := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveSecondCountableTopology F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  unfold leviFibreSmoothing
  rw [← integral_mul_left_eq_self _ a]
  exact integral_congr_ae (Eventually.of_forall fun b =>
    fam.leviFibreSmoothingIntegrand_mul_levi J T i hc β g a b x (w (a * b)))

omit [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant] in
/-- The smoothed function is left invariant on the standard parabolic quotient. -/
theorem isLeftInvariantUnder_leviFibreSmoothing (β : C_c(A, ℂ)) (w : Pos → V) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J))
      (fam.leviFibreSmoothing J T i hi I e hc β w) := by
  apply IsLeftInvariantUnder.sup
  · rintro _ ⟨u₀, rfl⟩ g
    unfold leviFibreSmoothing
    exact integral_congr_ae (Eventually.of_forall fun b =>
      fam.leviFibreSmoothingIntegrand_mul_radical J T i β g u₀ b 1 (w b))
  · rintro _ ⟨r, rfl⟩ g
    let x : A₁ := rationalNormOne F M r
    have hx : (x : AM) = rational F M r := rfl
    change fam.leviFibreSmoothing J T i hi I e hc β w (ι (x : AM) * g) = _
    unfold leviFibreSmoothing
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    change fam.leviFibreSmoothingIntegrand J T i β (ι (x : AM) * g) b 1 (w b) =
      fam.leviFibreSmoothingIntegrand J T i β g b 1 (w b)
    rw [fam.leviFibreSmoothingIntegrand_mul_normOne J T i hc β g b x (w b)]
    unfold leviFibreSmoothingIntegrand
    rw [hx, ← mul_one (rational F M r), normOnePartialConvolution_rational_mul]
    rfl

end Langlands.Global.StandardParabolicFamily
