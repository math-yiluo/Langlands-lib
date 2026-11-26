import Langlands.Automorphic.GroupSchemeCompactKernelDifferential
import Langlands.Global.AdelicInducedConvolutionCovariance
import Langlands.Global.AdelicGroupLocalPoints

/-! # Levi differential annihilators of induced convolution -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints
  Langlands.Geometry.Manifold

/-- Restrict an adelic function to the orbit of the infinite Levi through the specified point. -/
def infiniteLeviSlice {F : Type u} [Field F] [NumberField F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine M.X.left]
    (p : P ⟶ G) (l : M ⟶ P) (v : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    InfiniteAdelicGroupPoints F M → ℂ :=
  fun m => v (map F M G (l ≫ p) (ofInfinite F M m) * g)

/-- Any Levi enveloping operator annihilating all infinite Levi slices of the input also
annihilates all such slices of the integrated induced action. -/
def InducedConvolutionLeviAnnihilatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (l : M ⟶ P) (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    {d e : ℕ} (_hG : SmoothOfRelativeDimension d G.X.hom)
    (hM : SmoothOfRelativeDimension e M.X.hom) (hcalc : AdelicDifferentialCommutator F M hM)
    (D : AdelicEnvelopingAlgebra F M hM) (φ v : AdelicGroupPoints F G → ℂ),
    Continuous φ → HasCompactSupport φ → IsAdelicSmoothFunction F G v →
    (∀ (g : AdelicGroupPoints F G) (h : infiniteLeviSlice p l v g ∈ InfinitePlotSmoothFunctions F M),
      plotSmoothEnvelopingAction F M hM hcalc D ⟨infiniteLeviSlice p l v g, h⟩ = 0) →
    ∀ (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
      (h : infiniteLeviSlice p l (hK.inducedConvolution lam φ v) g ∈ InfinitePlotSmoothFunctions F M),
      plotSmoothEnvelopingAction F M hM hcalc D
        ⟨infiniteLeviSlice p l (hK.inducedConvolution lam φ v) g, h⟩ = 0

set_option maxHeartbeats 1000000 in
/-- On the Levi slice the twist multiplier is constant in the Levi variable. Use compact
integration of the slices of the input with that multiplier in the scalar weight. -/
theorem inducedConvolutionLeviAnnihilator : InducedConvolutionLeviAnnihilatorStatement.{u} := by
  intro F _ _ G P M _ _ _ _ p _ l K hK d e hG hM hcalc D φ v hφ hsupp hv hAnn lam g hg
  let := fun u : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F u
  let := smoothChartedSpace F G hG
  let := smoothChartedSpace F M hM
  let := smoothLieGroup F G hG
  let := smoothLieGroup F M hM
  let H := AdelicGroupPoints F G
  let Ginf := InfiniteAdelicGroupPoints F G
  let Minf := InfiniteAdelicGroupPoints F M
  let Gfin := FiniteAdelicGroupPoints F G
  let IG := 𝓘(ℝ, smoothModel F d)
  let IM := 𝓘(ℝ, smoothModel F e)
  let IC := 𝓘(ℝ, ℂ)
  let levi : Minf → Ginf := M.affinePointsTarget (l ≫ p) (CommAlgCat.of F (InfiniteAdeleRing F))
  have hlevi : ContMDiff IM IG ∞ levi := by
    apply (contMDiff_iff_coordinateSmooth F G IM hG _).mpr
    have hcoord := (contMDiff_iff_coordinateSmooth F M IM hM (id : Minf → Minf)).mp contMDiff_id
    exact hcoord.postcomp (l ≫ p).hom.hom
  obtain ⟨L, hL, hfix⟩ := hv.2.2
  let Q := Gfin ⧸ L
  let Z := Fin 0 → ℝ
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hL
  let : ChartedSpace Z Q := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ Q := IsManifold.of_discreteTopology ∞
  let : ChartedSpace (smoothModel F d × Z) (Ginf × Q) := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, smoothModel F d × Z) ∞ (Ginf × Q) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := IG) (I' := 𝓘(ℝ, Z)) Ginf Q
  let Ipar := 𝓘(ℝ, smoothModel F d × Z)
  let q : Gfin → Q := QuotientGroup.mk
  let kernel (z : Minf × (Ginf × Q)) : ℂ := v (pair F G (levi z.1 * z.2.1) z.2.2.out)
  have hkernel : ContMDiff (IM.prod Ipar) IC ∞ kernel := by
    dsimp only [Ipar]
    rw [modelWithCornersSelf_prod]
    intro z
    have hslice (b : Gfin) : ContMDiff IG IC ∞ (functionInfiniteSlice F G v b) :=
      (isPlotSmooth_iff_contMDiff F G hG _).mp (hv.2.1 b)
    have hv' := (hslice z.2.2.out).comp
      ((hlevi.comp contMDiff_fst).mul (contMDiff_fst.comp contMDiff_snd) :
        ContMDiff (IM.prod (IG.prod 𝓘(ℝ, Z))) IG ∞
          (fun y : Minf × (Ginf × Q) => levi y.1 * y.2.1))
    apply (hv' z).congr_of_eventuallyEq
    have hc : Continuous (fun y : Minf × (Ginf × Q) => y.2.2) :=
      continuous_snd.comp continuous_snd
    have he : ({z.2.2} : Set Q) ∈ 𝓝 z.2.2 := (isOpen_discrete _).mem_nhds (mem_singleton _)
    filter_upwards [(hc.tendsto z).eventually he] with y hy
    change y.2.2 = z.2.2 at hy
    change v (pair F G (levi y.1 * y.2.1) y.2.2.out) = _
    rw [hy]
    rfl
  let C := tsupport φ
  have hC : MeasurableSet C := hsupp.isClosed.measurableSet
  let : CompactSpace C := isCompact_iff_compactSpace.mp hsupp
  let haar : Measure H := Measure.haar
  let measure : Measure C := haar.comap Subtype.val
  let : IsFiniteMeasureOnCompacts measure := IsFiniteMeasureOnCompacts.comap' haar continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hC)
  let j : C(C, Ginf × Q) := ⟨fun z => (infinite F G (g * z.val), q (finite F G (g * z.val))), by
    have hc : Continuous (fun z : C => g * z.val) := continuous_const.mul continuous_subtype_val
    exact ((infinite F G).continuous.comp hc).prodMk
      (QuotientGroup.continuous_mk.comp ((finite F G).continuous.comp hc))⟩
  let twist (h : H) := Complex.exp (complexParameterPairing F P lam (hK.height (g * h) - hK.height g))
  have htwist : Continuous twist :=
    Complex.continuous_exp.comp ((continuous_complexParameterPairing lam).comp
      ((hK.continuous_height.comp (continuous_const.mul continuous_id)).sub continuous_const))
  let weight : C(C, ℂ) := ⟨fun z => φ z.val * twist z.val,
    (hφ.mul htwist).comp continuous_subtype_val⟩
  have hkSlice (z : C) (m : Minf) : kernel (m, j z) = infiniteLeviSlice p l v (g * z.val) m := by
    let x := g * z.val
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul (s := L) (finite F G x)
    have hpair : ofInfinite F G (levi m) * x =
        pair F G (levi m * infinite F G x) (finite F G x) := by
      rw [ofInfinite_eq_pair, ← one_mul (finite F G x), ← pair_mul, pair_projections]
    change v (pair F G (levi m * infinite F G x) (q (finite F G x)).out) =
      v (map F M G (l ≫ p) (ofInfinite F M m) * x)
    rw [map_ofInfinite, hpair, hb]
    simpa only [ofFinite_eq_pair, pair_mul, mul_one] using
      hfix b.val b.property (pair F G (levi m * infinite F G x) (finite F G x))
  have havg (m : Minf) : (∫ z : C, weight z • kernel (m, j z) ∂measure) =
      infiniteLeviSlice p l (hK.inducedConvolution lam φ v) g m := by
    let a := map F M P l (ofInfinite F M m)
    have ha : map F M G (l ≫ p) (ofInfinite F M m) = map F P G p a :=
      map_comp_apply_of_hom l (ofInfinite F M m)
    simp_rw [hkSlice]
    have hEq : (∫ z : C, weight z • infiniteLeviSlice p l v (g * z.val) m ∂measure) =
        ∫ z in C, (φ z * twist z) * infiniteLeviSlice p l v (g * z) m ∂haar := by
      change (∫ z : C, (φ z.val * twist z.val) * infiniteLeviSlice p l v (g * z.val) m ∂measure) = _
      exact integral_subtype_comap hC (fun z => (φ z * twist z) * infiniteLeviSlice p l v (g * z) m)
    rw [hEq, setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul])]
    change (∫ z, φ z * twist z * v (map F M G (l ≫ p) (ofInfinite F M m) * (g * z)) ∂haar) =
      ∫ z, φ z * hK.inducedRightTranslate lam z v (map F M G (l ≫ p) (ofInfinite F M m) * g) ∂haar
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change φ z * twist z * v (map F M G (l ≫ p) (ofInfinite F M m) * (g * z)) =
      φ z * hK.inducedRightTranslate lam z v (map F M G (l ≫ p) (ofInfinite F M m) * g)
    rw [ha, hK.inducedRightTranslate_eq_mul_exp_sub, mul_assoc (map F P G p a) g z,
      hK.height_map_mul, hK.height_map_mul, add_sub_add_left_eq_sub]
    change φ z * twist z * v (map F P G p a * (g * z)) =
      φ z * (v (map F P G p a * (g * z)) * twist z)
    ring
  obtain ⟨kD, _, hDslice, hDavg⟩ := compactKernelEnvelopingAction F M hM hcalc
    C (smoothModel F d × Z) (Ginf × Q) measure weight j D kernel hkernel
  have havgPlot : (fun m => ∫ z : C, weight z • kernel (m, j z) ∂measure) ∈
      InfinitePlotSmoothFunctions F M := (funext havg).symm ▸ hg
  have havgEq : (⟨fun m => ∫ z : C, weight z • kernel (m, j z) ∂measure, havgPlot⟩ :
      InfinitePlotSmoothFunctions F M) = ⟨infiniteLeviSlice p l (hK.inducedConvolution lam φ v) g, hg⟩ :=
    Subtype.ext (funext havg)
  have hDzero (z : C) (m : Minf) : kD (m, j z) = 0 := by
    have hk : (fun t => kernel (t, j z)) ∈ InfinitePlotSmoothFunctions F M :=
      (isPlotSmooth_iff_contMDiff F M hM _).mpr (hkernel.comp (contMDiff_id.prodMk contMDiff_const))
    have hl : infiniteLeviSlice p l v (g * z.val) ∈ InfinitePlotSmoothFunctions F M :=
      (funext (hkSlice z)) ▸ hk
    have heq : (⟨fun t => kernel (t, j z), hk⟩ : InfinitePlotSmoothFunctions F M) =
        ⟨infiniteLeviSlice p l v (g * z.val), hl⟩ := Subtype.ext (funext (hkSlice z))
    rw [← hDslice (j z) hk m, heq, hAnn (g * z.val) hl]
    rfl
  rw [← havgEq]
  apply Subtype.ext
  funext m
  rw [hDavg havgPlot m]
  simp only [hDzero, smul_zero, integral_zero, Submodule.coe_zero, Pi.zero_apply]

end Langlands.Global.AdelicGroupPoints
