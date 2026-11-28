import Langlands.Automorphic.GroupSchemeNormOneAtlas
import Langlands.Geometry.Manifold.GroupPathDerivative

/-! # Directional derivatives on the norm-one adelic group

For an embedded Lie atlas `A` on `G(F∞)¹`, a function `f` on `G(𝔸_F)¹` and a tangent vector `X`
at the identity of `G(F∞)¹`, `normOneDirectional A X f x` is the derivative at the identity of the
slice `a ↦ f (x a)` in the direction `X`. Words of such derivatives in the coordinate basis are the
operators `normOneDifferential A` of single words. -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d e : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}

local notation "G¹" => normOneSubgroup F G
local notation "G∞¹" => infiniteNormOneSubgroup F G
local notation "ι" => infiniteNormOneInclusion F G
local notation "IE" => 𝓘(ℝ, Fin e → ℝ)

/-- The derivative of `f` on `G(𝔸_F)¹` at `x` along the right orbit of `G(F∞)¹`, in the
direction of the tangent vector `X` at the identity. -/
def normOneDirectional (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ) (f : G¹ → ℂ)
    (x : G¹) : ℂ :=
  letI := A.chartedSpace
  letI := A.lieGroup
  groupDirectionalValue IE X (normOneInfiniteSlice F G f x) 1

/-- The slice through a right translate is the translated slice. -/
theorem normOneInfiniteSlice_mul (f : G¹ → ℂ) (x : G¹) (a b : G∞¹) :
    normOneInfiniteSlice F G f (x * ι a) b = normOneInfiniteSlice F G f x (a * b) := by
  simp only [normOneInfiniteSlice, map_mul, mul_assoc]

/-- The derivative at a right translate is the orbit derivative of the slice. -/
theorem normOneDirectional_mul (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    (f : G¹ → ℂ) (x : G¹) (a : G∞¹) :
    letI := A.chartedSpace
    letI := A.lieGroup
    normOneDirectional A X f (x * ι a) =
      groupDirectionalValue IE X (normOneInfiniteSlice F G f x) a := by
  have h : (fun b => normOneInfiniteSlice F G f (x * ι a) (1 * b)) =
      fun b => normOneInfiniteSlice F G f x (a * b) := by
    funext b
    rw [one_mul, normOneInfiniteSlice_mul]
  simp only [normOneDirectional, groupDirectionalValue]
  rw [h]

/-- The slice of the derivative is the orbit derivative of the slice. -/
theorem normOneInfiniteSlice_normOneDirectional (A : NormOneLieAtlas F G hsmooth e)
    (X : Fin e → ℝ) (f : G¹ → ℂ) (x : G¹) :
    letI := A.chartedSpace
    letI := A.lieGroup
    normOneInfiniteSlice F G (normOneDirectional A X f) x =
      groupDirectionalValue IE X (normOneInfiniteSlice F G f x) := by
  funext a
  exact normOneDirectional_mul A X f x a

/-- Left translation commutes with the derivative. -/
theorem normOneDirectional_mul_left (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    (f : G¹ → ℂ) (g₀ x : G¹) :
    normOneDirectional A X (fun y => f (g₀ * y)) x = normOneDirectional A X f (g₀ * x) := by
  have h : normOneInfiniteSlice F G (fun y => f (g₀ * y)) x =
      normOneInfiniteSlice F G f (g₀ * x) := by
    funext a
    simp only [normOneInfiniteSlice, mul_assoc]
  simp only [normOneDirectional]
  rw [h]

/-- The derivative is linear in the direction. -/
theorem normOneDirectional_eq_sum (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    (f : G¹ → ℂ) (x : G¹) :
    normOneDirectional A X f x =
      ∑ l : Fin e, (X l : ℂ) * normOneDirectional A (Pi.single l 1) f x := by
  let := A.chartedSpace
  let := A.lieGroup
  have hX : X = ∑ l : Fin e, X l • (Pi.single l (1 : ℝ) : Fin e → ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  unfold normOneDirectional groupDirectionalValue
  conv_lhs => rw [hX]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Complex.real_smul]

/-- Left invariance under the rational norm-one points is preserved by the derivative. -/
theorem normOneDirectional_rational (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    {f : G¹ → ℂ} (hf : ∀ (g₀ : rationalNormOneSubgroup F G) x, f ((g₀ : G¹) * x) = f x)
    (g₀ : rationalNormOneSubgroup F G) (x : G¹) :
    normOneDirectional A X f ((g₀ : G¹) * x) = normOneDirectional A X f x := by
  rw [← normOneDirectional_mul_left]
  congr 1
  funext y
  exact hf g₀ y

/-- Right invariance under a compact finite level is preserved by the derivative. -/
theorem normOneDirectional_level (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))} {f : G¹ → ℂ}
    (hf : ∀ (k : K₀) x, f (x * finiteLevelInclusion F G K₀ hK₀ k) = f x) (k : K₀) (x : G¹) :
    normOneDirectional A X f (x * finiteLevelInclusion F G K₀ hK₀ k) =
      normOneDirectional A X f x := by
  simp only [normOneDirectional]
  congr 1
  funext a
  simp only [normOneInfiniteSlice]
  have hc : (x * finiteLevelInclusion F G K₀ hK₀ k) * ι a = (x * ι a) * finiteLevelInclusion F G K₀ hK₀ k := by
    apply Subtype.ext
    change (x : AdelicGroupPoints F G) * ofFinite F G k.val * ofInfinite F G a.val =
      (x : AdelicGroupPoints F G) * ofInfinite F G a.val * ofFinite F G k.val
    rw [mul_assoc, mul_assoc, ← (factors_commute F G a.val k.val).eq]
  rw [hc, hf]

/-- **Finite-order regularity.** If `f` satisfies `IsNormOneCr A n K₀`, then its derivative in
any direction satisfies `IsNormOneCr A m K₀` for `m + 1 ≤ n ≤ ∞`. -/
theorem isNormOneCr_normOneDirectional (A : NormOneLieAtlas F G hsmooth e)
    {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n) (hn : n ≤ ∞) (X : Fin e → ℝ)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))} {f : G¹ → ℂ}
    (hf : IsNormOneCr A n K₀ hK₀ f) :
    IsNormOneCr A m K₀ hK₀ (normOneDirectional A X f) := by
  let := A.chartedSpace
  let := A.lieGroup
  refine ⟨normOneDirectional_rational A X hf.1, normOneDirectional_level A X hf.2.1, fun x => ?_⟩
  rw [normOneInfiniteSlice_normOneDirectional]
  exact contMDiff_groupDirectionalValue_of_le hmn hn X (hf.2.2 x)

/-- **Derivative along a path.** For a path `c` in `G(F∞)¹` differentiable at `t` and a function
whose slice at `x` is differentiable at `c t`, the derivative of `s ↦ f (x c(s))` at `t` is the
derivative of `f` at `x c(t)` in the direction `V` of the translated path velocity. -/
theorem hasDerivAt_normOne_path (A : NormOneLieAtlas F G hsmooth e) {f : G¹ → ℂ} {x : G¹}
    {c : ℝ → G∞¹} {t : ℝ} {V : Fin e → ℝ}
    (hV : letI := A.chartedSpace; letI := A.lieGroup; leftPathVelocity c t = V)
    (hf : letI := A.chartedSpace
      MDifferentiableAt IE 𝓘(ℝ, ℂ) (normOneInfiniteSlice F G f x) (c t))
    (hc : letI := A.chartedSpace; MDifferentiableAt 𝓘(ℝ, ℝ) IE c t) :
    HasDerivAt (fun s => f (x * ι (c s))) (normOneDirectional A V f (x * ι (c t))) t := by
  let := A.chartedSpace
  let := A.lieGroup
  have h := hasDerivAt_comp_path hf hc
  have h2 : normOneDirectional A V f (x * ι (c t)) =
      groupDirectionalValue IE V (normOneInfiniteSlice F G f x) (c t) :=
    normOneDirectional_mul A V f x (c t)
  rw [h2, ← hV]
  exact h

/-- **Difference quotients.** If the slice of `ψ` at `y` is differentiable at the identity, its
derivative in the direction `X` is the limit of the difference quotients along the chart line
`t ↦ χ⁻¹(χ(1) + t X)` of the extended chart `χ` at the identity, at the times `t = 1/(k+1)`. -/
theorem tendsto_normOneDirectional (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    {ψ : G¹ → ℂ} {y : G¹}
    (hd : letI := A.chartedSpace
      MDifferentiableAt IE 𝓘(ℝ, ℂ) (normOneInfiniteSlice F G ψ y) 1) :
    letI := A.chartedSpace
    Tendsto (fun k : ℕ => (((k : ℝ) + 1 : ℝ) : ℂ) *
        (ψ (y * ι ((extChartAt IE (1 : G∞¹)).symm
          (extChartAt IE (1 : G∞¹) 1 + ((k : ℝ) + 1)⁻¹ • X))) - ψ y))
      atTop (𝓝 (normOneDirectional A X ψ y)) := by
  let := A.chartedSpace
  let := A.lieGroup
  set χ := extChartAt IE (1 : G∞¹) with hχ
  let f := normOneInfiniteSlice F G ψ y
  have hfd := hd.hasMFDerivAt
  have h1 := hfd.2
  rw [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ] at h1
  have hw : writtenInExtChartAt IE 𝓘(ℝ, ℂ) 1 f = f ∘ χ.symm := by
    funext v
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.comp_apply, id_eq, χ]
  rw [hw] at h1
  have hline : HasDerivAt (fun t : ℝ => χ 1 + t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (χ 1)
  have hcomp := h1.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp [χ])
  have hslope := hcomp.tendsto_slope_zero
  have hseq : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · exact inv_ne_zero (by positivity)
  have hlim := hslope.comp hseq
  have hval : normOneDirectional A X ψ y = (mfderiv IE 𝓘(ℝ, ℂ) f 1 : (Fin e → ℝ) →L[ℝ] ℂ) X := by
    simp only [normOneDirectional, groupDirectionalValue, one_mul]
    rfl
  rw [hval]
  refine hlim.congr fun k => ?_
  have h0 : f (χ.symm (χ 1 + (0 : ℝ) • X)) = ψ y := by
    simp only [zero_smul, add_zero, χ, extChartAt_to_inv, f,
      normOneInfiniteSlice, map_one, mul_one]
  simp only [Function.comp_apply, zero_add, inv_inv]
  rw [h0, Complex.real_smul]
  push_cast
  rfl

/-- **Joint measurability of derivatives of a family.** -/
theorem measurable_normOneDirectional (A : NormOneLieAtlas F G hsmooth e) (X : Fin e → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {ψ : Ω → G¹ → ℂ}
    (hm : Measurable (fun p : Ω × G¹ => ψ p.1 p.2))
    (hd : letI := A.chartedSpace
      ∀ o y, MDifferentiableAt IE 𝓘(ℝ, ℂ) (normOneInfiniteSlice F G (ψ o) y) 1) :
    Measurable (fun p : Ω × G¹ => normOneDirectional A X (ψ p.1) p.2) := by
  let := A.chartedSpace
  set χ := extChartAt IE (1 : G∞¹)
  let b (k : ℕ) : G∞¹ := χ.symm (χ 1 + ((k : ℝ) + 1)⁻¹ • X)
  refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) (p : Ω × G¹) =>
    (((k : ℝ) + 1 : ℝ) : ℂ) * (ψ p.1 (p.2 * ι (b k)) - ψ p.1 p.2)) ?_ ?_
  · intro k
    have hr : Measurable fun z : G¹ => z * ι (b k) := (continuous_id.mul continuous_const).measurable
    exact measurable_const.mul ((hm.comp (measurable_fst.prodMk (hr.comp measurable_snd))).sub hm)
  · exact tendsto_pi_nhds.mpr fun p => tendsto_normOneDirectional A X (hd p.1 p.2)

end Langlands.Automorphic.GroupSchemeFunctions
