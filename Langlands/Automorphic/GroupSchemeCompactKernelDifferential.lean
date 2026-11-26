import Langlands.Analysis.CompactManifoldVectorIntegral
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.Automorphic.GroupSchemeEnvelopingAction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Differentiation of weighted compact integrals of smooth adelic slices -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Analysis Langlands.Geometry.Manifold Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

section Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {S N : Type*} [TopologicalSpace S] [TopologicalSpace N] [Group S]
  [ChartedSpace E S] [ChartedSpace H N] [LieGroup 𝓘(ℝ, E) ∞ S]
  [IsManifold 𝓘(ℝ, H) ∞ N]

local notation "IS" => 𝓘(ℝ, E)
local notation "IN" => 𝓘(ℝ, H)
local notation "IC" => 𝓘(ℝ, ℂ)

private def kernelDirectionalValue (X : GroupLieAlgebra IS S) (k : S × N → ℂ)
    (p : S × N) : ℂ :=
  groupDirectionalValue IS X (fun x => k (x, p.2)) p.1

omit [FiniteDimensional ℝ E] in
/-- Differentiation in the first variable preserves joint smoothness. -/
private theorem contMDiff_kernelDirectionalValue (X : GroupLieAlgebra IS S)
    {k : S × N → ℂ} (hk : ContMDiff ((IS).prod IN) IC ∞ k) :
    ContMDiff ((IS).prod IN) IC ∞ (kernelDirectionalValue X k) := by
  let k' (p : (S × N) × S) := k (p.1.1 * p.2, p.1.2)
  have hm : ContMDiff (((IS).prod IN).prod IS) IS ∞
      (fun p : (S × N) × S => p.1.1 * p.2) := (contMDiff_fst.comp contMDiff_fst).mul contMDiff_snd
  have hk' : ContMDiff (((IS).prod IN).prod IS) IC ∞ k' :=
    hk.comp (hm.prodMk (contMDiff_snd.comp contMDiff_fst))
  let B := (IS).prod IN
  let f₁ (p : S × N) : TangentBundle B (S × N) := Bundle.TotalSpace.mk' (E × H) p 0
  let f₂ (_ : S × N) : TangentBundle IS S := Bundle.TotalSpace.mk' E 1 X
  have hf₁ : ContMDiff B B.tangent ∞ f₁ := Bundle.contMDiff_zeroSection _ _
  have hf₂ : ContMDiff B (IS).tangent ∞ f₂ := contMDiff_const
  let combine : TangentBundle B (S × N) × TangentBundle IS S →
      TangentBundle (B.prod IS) ((S × N) × S) := (equivTangentBundleProd B (S × N) IS S).symm
  have hcombine : ContMDiff (B.tangent.prod (IS).tangent) (B.prod IS).tangent ∞ combine :=
    contMDiff_equivTangentBundleProd_symm
  have hderiv := (contMDiff_snd_tangentBundle_modelSpace ℂ IC).comp
    ((hk'.contMDiff_tangentMap (m := ∞) (by simp)).comp (hcombine.comp (hf₁.prodMk hf₂)))
  convert hderiv using 1
  funext p
  dsimp [Function.comp_def, f₁, f₂, combine, tangentMap]
  rw [mfderiv_prod_eq_add_apply (hk'.mdifferentiableAt (by simp))]
  simp +instances [kernelDirectionalValue, groupDirectionalValue, mvfderiv, equivTangentBundleProd]
  rfl

variable {C : Type*} [TopologicalSpace C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
  (measure : Measure C) [IsFiniteMeasure measure] (a : C(C, ℂ)) (j : C(C, N))

/-- Differentiation in the first variable passes through the compact weighted integral. -/
private theorem groupDirectionalValue_compactIntegral {k : S × N → ℂ}
    (hk : ContMDiff ((IS).prod IN) IC ∞ k) (X : GroupLieAlgebra IS S) (x : S) :
    groupDirectionalValue IS X (fun y => ∫ z, a z • k (y, j z) ∂measure) x =
      ∫ z, a z • kernelDirectionalValue X k (x, j z) ∂measure := by
  let k' (p : S × N) := k (x * p.1, p.2)
  have hk' : ContMDiff ((IS).prod IN) IC ∞ k' :=
    hk.comp ((contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd)
  exact (compactManifoldVectorIntegral C E S H N ℂ measure a j k' hk').2.2.2 1 X

end Manifold

universe u uC uH uN

/-- Applying an actual enveloping operator to the first variable of a smooth joint kernel
preserves joint smoothness and commutes with compact weighted integration. -/
def CompactKernelEnvelopingActionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (C : Type uC) [TopologicalSpace C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (N : Type uN) [TopologicalSpace N] [ChartedSpace H N] [IsManifold 𝓘(ℝ, H) ∞ N]
    (measure : Measure C) [IsFiniteMeasure measure] (a : C(C, ℂ)) (j : C(C, N)),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∀ (D : AdelicEnvelopingAlgebra F G hsmooth)
      (k : InfiniteAdelicGroupPoints F G × N → ℂ),
      ContMDiff (𝓘(ℝ, smoothModel F d).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞ k →
      ∃ kD : InfiniteAdelicGroupPoints F G × N → ℂ,
        ContMDiff (𝓘(ℝ, smoothModel F d).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞ kD ∧
        (∀ (y : N)
          (h : (fun x => k (x, y)) ∈ InfinitePlotSmoothFunctions F G)
          (x : InfiniteAdelicGroupPoints F G),
          (plotSmoothEnvelopingAction F G hsmooth hcalc D ⟨fun t => k (t, y), h⟩).val x = kD (x, y)) ∧
        ∀ (h : (fun x => ∫ z, a z • k (x, j z) ∂measure) ∈ InfinitePlotSmoothFunctions F G)
          (x : InfiniteAdelicGroupPoints F G),
          (plotSmoothEnvelopingAction F G hsmooth hcalc D
            ⟨fun t => ∫ z, a z • k (t, j z) ∂measure, h⟩).val x =
              ∫ z, a z • kD (x, j z) ∂measure

set_option maxHeartbeats 800000 in
/-- Reduce to real tangent derivatives and extend by the generators of the enveloping algebra. -/
theorem compactKernelEnvelopingAction : CompactKernelEnvelopingActionStatement.{u,uC,uH,uN} := by
  intro F _ _ G _ d hsmooth hcalc C _ _ _ _ H _ _ N _ _ _ measure _ a j
  let S := InfiniteAdelicGroupPoints F G
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) S := LieGroup.of_le (n := ∞) (by simp)
  let I := 𝓘(ℝ, smoothModel F d)
  let I' := 𝓘(ℝ, H)
  let V := InfinitePlotSmoothFunctions F G
  let U := AdelicEnvelopingAlgebra F G hsmooth
  let act := plotSmoothEnvelopingAction F G hsmooth hcalc
  let avg (k : S × N → ℂ) (x : S) := ∫ z, a z • k (x, j z) ∂measure
  let smooth (k : S × N → ℂ) := ContMDiff (I.prod I') 𝓘(ℝ, ℂ) ∞ k
  let condition (D : U) := ∀ (k : S × N → ℂ), smooth k →
    ∃ kD : S × N → ℂ, smooth kD ∧
      (∀ (y : N) (h : (fun x => k (x, y)) ∈ V) (x : S),
        (act D ⟨fun t => k (t, y), h⟩).val x = kD (x, y)) ∧
      ∀ (h : avg k ∈ V) (x : S), (act D ⟨avg k, h⟩).val x = avg kD x
  change ∀ D : U, condition D
  have havg {k : S × N → ℂ} (hk : smooth k) : avg k ∈ V :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
      (compactManifoldVectorIntegral C (smoothModel F d) S H N ℂ measure a j k hk).2.1
  have hslice {k : S × N → ℂ} (hk : smooth k) (y : N) : (fun x => k (x, y)) ∈ V :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
      (hk.comp (contMDiff_id.prodMk contMDiff_const))
  have hint {k : S × N → ℂ} (hk : smooth k) (x : S) :
      Integrable (fun z => a z • k (x, j z)) measure :=
    (compactManifoldVectorIntegral C (smoothModel F d) S H N ℂ measure a j k hk).1 x
  have hone : condition 1 := by
    intro k hk
    exact ⟨k, hk, fun y h x => by simp [map_one], fun h x => by simp [map_one]⟩
  have hsmul (z : ℂ) (D : U) (hD : condition D) : condition (z • D) := by
    intro k hk
    obtain ⟨kD, hkD, hDslice, hDavg⟩ := hD k hk
    have hz : ContDiff ℝ ∞ (fun c : ℂ => z • c) :=
      ((ContinuousLinearMap.mul ℝ ℂ) z).contDiff
    refine ⟨fun p => z • kD p, hz.contMDiff.comp hkD, fun y hy x => ?_, fun h x => ?_⟩
    · rw [map_smul]
      change z • (act D ⟨fun t => k (t, y), hy⟩).val x = _
      rw [hDslice y hy x]
    · rw [map_smul]
      change z • (act D ⟨avg k, h⟩).val x = avg (fun p => z • kD p) x
      rw [hDavg h x]
      unfold avg
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z' => smul_comm z (a z') _
  have hadd (D E : U) (hD : condition D) (hE : condition E) : condition (D + E) := by
    intro k hk
    obtain ⟨kD, hkD, hDslice, hDavg⟩ := hD k hk
    obtain ⟨kE, hkE, hEslice, hEavg⟩ := hE k hk
    refine ⟨fun p => kD p + kE p, hkD.add hkE, fun y hy x => ?_, fun h x => ?_⟩
    · rw [map_add]
      change (act D ⟨fun t => k (t, y), hy⟩).val x + (act E ⟨fun t => k (t, y), hy⟩).val x = _
      rw [hDslice y hy x, hEslice y hy x]
    · rw [map_add]
      change (act D ⟨avg k, h⟩).val x + (act E ⟨avg k, h⟩).val x =
        avg (fun p => kD p + kE p) x
      rw [hDavg h x, hEavg h x]
      unfold avg
      simp_rw [smul_add]
      exact (integral_add (hint hkD x) (hint hkE x)).symm
  have hmul (D E : U) (hD : condition D) (hE : condition E) : condition (D * E) := by
    intro k hk
    obtain ⟨kE, hkE, hEslice, hEavg⟩ := hE k hk
    obtain ⟨kDE, hkDE, hDEslice, hDEavg⟩ := hD kE hkE
    refine ⟨kDE, hkDE, fun y hy x => ?_, fun h x => ?_⟩
    · have he : act E ⟨fun t => k (t, y), hy⟩ = ⟨fun t => kE (t, y), hslice hkE y⟩ :=
        Subtype.ext (funext (hEslice y hy))
      rw [map_mul, Module.End.mul_apply, he, hDEslice]
    · have he : act E ⟨avg k, h⟩ = ⟨avg kE, havg hkE⟩ := Subtype.ext (funext (hEavg h))
      rw [map_mul, Module.End.mul_apply, he, hDEavg]
  have hreal (X : GroupLieAlgebra I S) : condition
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) := by
    intro k hk
    refine ⟨kernelDirectionalValue X k, contMDiff_kernelDirectionalValue X hk, ?_, ?_⟩
    · intro y hy x
      unfold act
      rw [plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul, one_smul]
      rfl
    · intro h x
      unfold act
      rw [plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul, one_smul]
      exact groupDirectionalValue_compactIntegral measure a j hk X x
  have hgen (x : ℂ ⊗[ℝ] GroupLieAlgebra I S) :
      condition (UniversalEnvelopingAlgebra.ι ℂ x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c X =>
      have hc : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul]
      exact hsmul c _ (hreal X)
    | add X Y hX hY =>
      rw [map_add]
      exact hadd _ _ hX hY
  intro D
  obtain ⟨q, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] GroupLieAlgebra I S)) D
  induction q using TensorAlgebra.induction with
  | algebraMap z =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact hsmul z 1 hone
  | «ι» X => exact hgen X
  | mul p q hp hq => rw [map_mul]; exact hmul _ _ hp hq
  | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq

end Langlands.Automorphic.GroupSchemeFunctions
