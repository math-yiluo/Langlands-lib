import Langlands.Global.AdelicHarishChandraFiniteCompactChange
import Langlands.Global.AdelicIwasawaSmoothHeightStatement
import Langlands.Global.AdelicTwistedConvolution

/-! # Parabolic fibres and finite levels of transported right convolution -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField
open scoped CategoryTheory.MonObj ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "Param" => ComplexCharacterParameter F P
local notation "μ" => (Measure.haar : Measure A)

omit [LocallyOfFiniteType G.X.hom] in
/-- The weight for transported convolution on the left parabolic fibre through `x`. -/
def IsIwasawaCompact.parabolicFibreKernel (h : A → ℂ) (lam : Param) (x : A) (t : A) : ℂ :=
  h t * (hK.heightPower lam (x * t) / hK.heightPower lam x)

omit [LocallyOfFiniteType G.X.hom] in
theorem IsIwasawaCompact.continuous_parabolicFibreKernel {h : A → ℂ} (hh : Continuous h)
    (lam : Param) (x : A) : Continuous (hK.parabolicFibreKernel h lam x) :=
  hh.mul (((hK.continuous_heightPower lam).comp (continuous_const.mul continuous_id)).div_const _)

omit [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
  [IsClosedImmersion p.hom.hom.left] in
theorem IsIwasawaCompact.hasCompactSupport_parabolicFibreKernel {h : A → ℂ}
    (hh : HasCompactSupport h) (lam : Param) (x : A) :
    HasCompactSupport (hK.parabolicFibreKernel h lam x) :=
  hh.mul_right

omit [LocallyOfFiniteType G.X.hom] in
/-- The quotient of the height powers at `x * t` and `x` is constant along each
left `P(𝔸)` orbit. -/
theorem IsIwasawaCompact.heightPower_ratio_map_mul (lam : Param)
    (q : AdelicGroupPoints F P) (x t : A) :
    hK.heightPower lam (map F P G p q * x * t) /
        hK.heightPower lam (map F P G p q * x) =
      hK.heightPower lam (x * t) / hK.heightPower lam x := by
  let c := Complex.exp (complexParameterPairing F P lam (characterLog F P q))
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have he (y : A) : hK.heightPower lam (map F P G p q * y) = c * hK.heightPower lam y := by
    simp only [IsIwasawaCompact.heightPower, c, hK.height_map_mul, map_add, Complex.exp_add]
  rw [mul_assoc, he, he, mul_div_mul_left _ _ hc]

/-- On a left parabolic fibre, transported convolution integrates the restrictions of
the original function with a scalar weight depending only on the base point and kernel
variable. -/
theorem IsIwasawaCompact.twistedConvolutionEnd_map_mul {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (lam : Param) (f : C(A, ℂ))
    (q : AdelicGroupPoints F P) (x : A) :
    hK.twistedConvolutionEnd hsmooth hh lam f (map F P G p q * x) =
      ∫ t, hK.parabolicFibreKernel h lam x t * f (map F P G p q * (x * t)) ∂μ := by
  rw [hK.twistedConvolutionEnd_apply, rightConvolution, ← integral_div]
  apply integral_congr_ae
  filter_upwards with t
  have hratio := hK.heightPower_ratio_map_mul lam q x t
  rw [mul_assoc (map F P G p q) x t] at hratio
  rw [mul_assoc (map F P G p q) x t, IsIwasawaCompact.parameterTwist]
  calc
    _ = (h t * (hK.heightPower lam (map F P G p q * (x * t)) /
          hK.heightPower lam (map F P G p q * x))) * f (map F P G p q * (x * t)) := by ring
    _ = _ := by rw [hratio, IsIwasawaCompact.parabolicFibreKernel]

/-- A test kernel with support over a finite subgroup acts on right invariants of that
subgroup under transported convolution whenever the height is invariant there. -/
theorem IsIwasawaCompact.twistedConvolutionEnd_rightInvariant {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (L : Subgroup Af)
    (hLK : L ≤ K.comap (ofFinite F G).toMonoidHom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (hs : ∀ t, h t ≠ 0 → finite F G t ∈ L)
    (lam : Param) {f : C(A, ℂ)} (hf : ∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) :
    ∀ l ∈ L, ∀ x, hK.twistedConvolutionEnd hsmooth hh lam f (x * ofFinite F G l) =
      hK.twistedConvolutionEnd hsmooth hh lam f x := by
  intro l hl x
  have hheight (b : Af) (hb : b ∈ L) (g : A) :
      hK.heightPower lam (g * ofFinite F G b) = hK.heightPower lam g :=
    congrArg (fun y => Complex.exp (complexParameterPairing F P lam y))
      (hK.height_mul_right g (hLK hb))
  rw [hK.twistedConvolutionEnd_apply, hK.twistedConvolutionEnd_apply, hheight l hl]
  congr 1
  unfold rightConvolution
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : h t = 0
  · simp only [ht, zero_mul]
  · let b := finite F G t
    let l' := b⁻¹ * l * b
    have hb : b ∈ L := hs t ht
    have hl' : l' ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hb) hl) hb
    have hcomm : ofFinite F G l * t = t * ofFinite F G l' := by
      conv_lhs => rw [← pair_projections F G t]
      conv_rhs => rw [← pair_projections F G t]
      simp only [ofFinite_eq_pair, pair_mul, one_mul, mul_one]
      congr 1
      change l * b = b * (b⁻¹ * l * b)
      group
    rw [mul_assoc x, hcomm, ← mul_assoc x, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.parameterTwist, hf l' hl', hheight l' hl']

/-- The transported operator has smooth infinite slices when the height pairings
are smooth, irrespective of the input's archimedean smoothness. -/
theorem IsIwasawaCompact.twistedConvolutionEnd_smoothSlice {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hH : hK.HasSmoothHeightPairings hsmooth)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : Param) (f : C(A, ℂ))
    (b : Af) : functionInfiniteSlice F G (hK.twistedConvolutionEnd hsmooth hh lam f) b ∈
      InfinitePlotSmoothFunctions F G := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let v := hK.continuousParameterTwist lam f
  let w := rightConvolution F G h v
  have hw := (adelicRightConvolutionDifferentiation F G d hsmooth h v hh v.continuous.measurable
    v.continuous.locallyIntegrable).2.1.2.1
  have hfib : functionInfiniteSlice F G (hK.twistedConvolutionEnd hsmooth hh lam f) b =
      functionInfiniteSlice F G (hK.parameterTwist w (-lam)) b := by
    funext a
    change hK.twistedConvolutionEnd hsmooth hh lam f (pair F G a b) = _
    rw [hK.twistedConvolutionEnd_apply]
    change w (pair F G a b) / hK.heightPower lam (pair F G a b) = _
    simp only [functionInfiniteSlice, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply, Complex.exp_neg, div_eq_mul_inv]
  rw [hfib]
  apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
  exact hK.contMDiff_parameterTwist_slice hsmooth hH w (-lam)
    (fun c => (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hw c)) b

/-- With equal infinite compact factors, the transported operators coincide for
kernels supported over the intersection of the finite compact factors. -/
theorem IsIwasawaCompact.twistedConvolutionEnd_eq_of_finite_support {d : ℕ}
    {K' : Subgroup A} (hK' : IsIwasawaCompact p K')
    (hmax : IsMaximalCompactSubgroup F G K) (hmax' : IsMaximalCompactSubgroup F G K')
    (hArch : K.map (infinite F G).toMonoidHom = K'.map (infinite F G).toMonoidHom)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (hs : ∀ t, h t ≠ 0 → finite F G t ∈ K.map (finite F G).toMonoidHom ⊓
      K'.map (finite F G).toMonoidHom)
    (lam : Param) :
    hK.twistedConvolutionEnd hsmooth hh lam = hK'.twistedConvolutionEnd hsmooth hh lam := by
  ext1 f
  apply ContinuousMap.ext
  intro x
  rw [hK.twistedConvolutionEnd_apply, hK'.twistedConvolutionEnd_apply,
    hK.rightConvolution_parameterTwist_of_finite_support hK' hmax hmax' hArch hs]
  let c := Complex.exp (complexParameterPairing F P lam (hK.height x - hK'.height x))
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hprod : hK.heightPower lam x = c * hK'.heightPower lam x := by
    unfold IsIwasawaCompact.heightPower c
    rw [← Complex.exp_add, ← map_add, sub_add_cancel]
  change (c * _) / hK.heightPower lam x = _
  rw [hprod, mul_div_mul_left _ _ hc]

end Langlands.Global.AdelicGroupPoints
