import Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth
import Langlands.Global.AdelicIwasawaSmoothHeight
import Langlands.Global.AdelicEisensteinCentralCovariance

/-! # Derivative bounds for the height-twisted inducing function -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "H" => InfiniteAdelicGroupPoints F G
local notation "FinPts" => FiniteAdelicGroupPoints F G
local notation "E" => smoothModel F d
local notation "IH" => 𝓘(ℝ, E)
local notation "U" => AdelicEnvelopingAlgebra F G hsmooth
local notation "S" => InfinitePlotSmoothFunctions F G

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual enveloping derivatives commute with pullback by left multiplication
on the archimedean smooth carrier. -/
theorem plotSmoothEnvelopingAction_leftTranslate (x : H) (a : U) (f : S) :
    plotSmoothEnvelopingAction F G hsmooth hcalc a (plotSmoothLeftTranslation F G x f) =
      plotSmoothLeftTranslation F G x (plotSmoothEnvelopingAction F G hsmooth hcalc a f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let X := Module.finBasis ℝ E
  obtain ⟨q, rfl⟩ := wordHom_surjective F G hsmooth X X.span_eq a
  apply Subtype.ext
  funext y
  rw [plotSmoothLeftTranslation_apply, plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc,
    plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc]
  exact lieWordAction_leftTranslation X q x f.val y

private def mulSmoothSlices (f h : S) : S := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let hf := (isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property
  let hh := (isPlotSmooth_iff_contMDiff F G hsmooth _).mp h.property
  refine ⟨fun x => f.val x * h.val x, ?_⟩
  exact (isPlotSmooth_iff_contMDiff F G hsmooth (fun x => f.val x * h.val x)).mpr
    ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp (hf.prodMk_space hh))

private theorem plotSmoothDifferential_mulSmoothSlices (X : E) (f h : S) :
    plotSmoothDifferential F G hsmooth X (mulSmoothSlices F G hsmooth f h) =
      mulSmoothSlices F G hsmooth (plotSmoothDifferential F G hsmooth X f) h +
        mulSmoothSlices F G hsmooth f (plotSmoothDifferential F G hsmooth X h) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  apply Subtype.ext
  funext x
  let p (y : H) := f.val (x * y)
  let q (y : H) := h.val (x * y)
  have hx : ContMDiff IH IH ∞ (fun y : H => x * y) := contMDiff_const.mul contMDiff_id
  have hp : MDifferentiableAt IH 𝓘(ℝ, ℂ) p 1 :=
    (((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property).comp hx).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt IH 𝓘(ℝ, ℂ) q 1 :=
    (((isPlotSmooth_iff_contMDiff F G hsmooth _).mp h.property).comp hx).mdifferentiableAt (by simp)
  have hD : mvfderiv IH (p * q) 1 = p 1 • mvfderiv IH q 1 + q 1 • mvfderiv IH p 1 :=
    (hp.hasMFDerivAt.mul hq.hasMFDerivAt).mfderiv
  change mvfderiv IH (p * q) 1 X = mvfderiv IH p 1 X * h.val x + f.val x * mvfderiv IH q 1 X
  rw [hD]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [show p 1 = f.val x from congrArg f.val (mul_one x),
    show q 1 = h.val x from congrArg h.val (mul_one x)]
  ring

include hcalc in
/-- If the derivative bounds for two slice families use the weights `w₁` and `w₂`,
all derivatives of their product use `w₁ * w₂`. -/
private theorem exists_enveloping_bound_mul (f h : FinPts → S) (w₁ w₂ : FinPts → H → ℝ)
    (hf : ∀ a : U, ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a (f b)).val x‖ ≤ C * w₁ b x)
    (hh : ∀ a : U, ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a (h b)).val x‖ ≤ C * w₂ b x)
    (h₁ : ∀ b x, 0 ≤ w₁ b x) (a : U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a
        (mulSmoothSlices F G hsmooth (f b) (h b))).val x‖ ≤ C * (w₁ b x * w₂ b x) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup IH (minSmoothness ℝ 3) H := LieGroup.of_le (n := ∞) (by simp)
  let Act := plotSmoothEnvelopingAction F G hsmooth hcalc
  let A := sliceFamilyEnvelopingAction F G hsmooth hcalc
  let V := FinPts → S
  let product (a₁ a₂ : U) : V := fun b => mulSmoothSlices F G hsmooth (Act a₁ (f b)) (Act a₂ (h b))
  let W : Submodule ℂ V := Submodule.span ℂ (Set.range fun p : U × U => product p.1 p.2)
  have hs (a₁ a₂ : U) : product a₁ a₂ ∈ W := Submodule.subset_span ⟨(a₁, a₂), rfl⟩
  let gen (X : E) : U := UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
  have hgen (X : E) (v : V) (hv : v ∈ W) : A (gen X) v ∈ W := by
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a₁, a₂⟩, rfl⟩ := hz
      have he : A (gen X) (product a₁ a₂) = product (gen X * a₁) a₂ + product a₁ (gen X * a₂) := by
        funext b
        change Act (gen X) (mulSmoothSlices F G hsmooth (Act a₁ (f b)) (Act a₂ (h b))) =
          mulSmoothSlices F G hsmooth (Act (gen X * a₁) (f b)) (Act a₂ (h b)) +
            mulSmoothSlices F G hsmooth (Act a₁ (f b)) (Act (gen X * a₂) (h b))
        simp only [map_mul, Module.End.mul_apply, gen, Act, plotSmoothEnvelopingAction_real_generator,
          plotSmoothDifferential_mulSmoothSlices]
      rw [he]
      exact W.add_mem (hs _ _) (hs _ _)
    | zero => simpa only [map_zero] using W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let X := Module.finBasis ℝ E
  have hstable (u : U) (v : V) (hv : v ∈ W) : A u v ∈ W := by
    obtain ⟨q, rfl⟩ := wordHom_surjective F G hsmooth X X.span_eq u
    induction q using MonoidAlgebra.induction_linear with
    | zero => simpa only [map_zero, LinearMap.zero_apply] using W.zero_mem
    | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply]
      exact W.add_mem hp hq
    | single w c =>
      have hword (w : FreeMonoid (Fin (Module.finrank ℝ E))) :
          A (wordHom F G hsmooth X (MonoidAlgebra.single w 1)) v ∈ W := by
        induction w using FreeMonoid.inductionOn' with
        | one => simpa only [← MonoidAlgebra.one_def, map_one, Module.End.one_apply] using hv
        | of_mul i w ih =>
          rw [show MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℂ) =
              MonoidAlgebra.single (FreeMonoid.of i) 1 * MonoidAlgebra.single w 1 by
                rw [MonoidAlgebra.single_mul_single, one_mul],
            map_mul, map_mul, Module.End.mul_apply, wordHom_of]
          exact hgen (X i) _ ih
      rw [show MonoidAlgebra.single w c = c • MonoidAlgebra.single w (1 : ℂ) by
        rw [MonoidAlgebra.smul_single', mul_one], map_smul, map_smul, LinearMap.smul_apply]
      exact W.smul_mem c (hword w)
  have hbound (v : V) (hv : v ∈ W) : ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(v b).val x‖ ≤ C * (w₁ b x * w₂ b x) := by
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a₁, a₂⟩, rfl⟩ := hz
      obtain ⟨C, hC, hc⟩ := hf a₁
      obtain ⟨D, hD, hd⟩ := hh a₂
      refine ⟨C * D, mul_nonneg hC hD, fun b x => ?_⟩
      change ‖(Act a₁ (f b)).val x * (Act a₂ (h b)).val x‖ ≤ _
      rw [norm_mul, mul_mul_mul_comm C D]
      exact mul_le_mul (hc b x) (hd b x) (norm_nonneg _) (mul_nonneg hC (h₁ b x))
    | zero => exact ⟨0, le_rfl, fun _ _ => by change ‖(0 : ℂ)‖ ≤ _; simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨C, hC, hc⟩ := hv
      obtain ⟨D, hD, hd⟩ := hw
      refine ⟨C + D, add_nonneg hC hD, fun b x => ?_⟩
      change ‖(v b).val x + (w b).val x‖ ≤ _
      rw [add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hc b x) (hd b x))
    | smul z v _ hv =>
      obtain ⟨C, hC, hc⟩ := hv
      refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC, fun b x => ?_⟩
      change ‖z * (v b).val x‖ ≤ _
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hc b x) (norm_nonneg _)
  simpa only [product, Act, A, map_one, Module.End.one_apply, sliceFamilyEnvelopingAction_apply] using
    hbound (A a (product 1 1)) (hstable a _ (hs 1 1))

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

open Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold InfiniteAdelicGroupPoints
open Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hmax : IsMaximalCompactSubgroup F G K)
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "H" => InfiniteAdelicGroupPoints F G
local notation "FinPts" => FiniteAdelicGroupPoints F G
local notation "U" => AdelicEnvelopingAlgebra F G hsmooth
local notation "S" => InfinitePlotSmoothFunctions F G

private def heightPowerSlice (hH : hK.HasSmoothHeightPairings hsmooth)
    (lam : ComplexCharacterParameter F P) (b : FinPts) : S := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  refine ⟨fun x => hK.heightPower lam (pair F G x b), ?_⟩
  exact (isPlotSmooth_iff_contMDiff F G hsmooth (fun x => hK.heightPower lam (pair F G x b))).mpr
    ((Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).contMDiff.comp (hH lam b))

include hmax in
private theorem exists_enveloping_heightPowerSlice_bound (hH : hK.HasSmoothHeightPairings hsmooth)
    (lam : ComplexCharacterParameter F P) (a : U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a (hK.heightPowerSlice hsmooth hH lam b)).val x‖ ≤
        C * ‖hK.heightPower lam (pair F G x b)‖ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let Act := plotSmoothEnvelopingAction F G hsmooth hcalc
  let h := hK.heightPowerSlice hsmooth hH lam
  let f : H → ℂ := (Act a (h 1)).val
  have hf : Continuous f :=
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp (Act a (h 1)).property).continuous
  obtain ⟨C, hC⟩ := (hK.isCompact.image ((hf.comp (infinite F G).continuous).norm)).bddAbove
  refine ⟨max 0 C, le_max_left _ _, fun b x => ?_⟩
  obtain ⟨q, k, hk, heq⟩ := hK.exists_eq (pair F G x b)
  let z := parameterPower F P lam q
  have hk₂ : ofFinite F G (finite F G k) ∈ K := ((hmax.mem_iff k).mp hk).2
  have htrans : plotSmoothLeftTranslation F G x (h b) =
      z • plotSmoothLeftTranslation F G (infinite F G k) (h 1) := by
    apply Subtype.ext
    funext y
    change hK.heightPower lam (pair F G (x * y) b) =
      z * hK.heightPower lam (pair F G (infinite F G k * y) 1)
    have hsplit : k * ofInfinite F G y =
        pair F G (infinite F G k * y) 1 * ofFinite F G (finite F G k) := by
      conv_lhs => rw [← pair_projections F G k]
      simp only [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
    calc
      _ = hK.heightPower lam ((map F P G p q * k) * ofInfinite F G y) := by
        rw [heq, ofInfinite_eq_pair, pair_mul, mul_one]
      _ = _ := by
        rw [mul_assoc, hK.heightPower_map_mul, hsplit, heightPower, hK.height_mul_right _ hk₂]
        rfl
  have hd : (Act a (h b)).val x = z * f (infinite F G k) := by
    have he := congrArg (fun s : S => (Act a s).val 1) htrans
    simpa only [Act, plotSmoothEnvelopingAction_leftTranslate F G hsmooth hcalc,
      plotSmoothLeftTranslation_apply, map_smul, mul_one, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, f] using he
  have hz : hK.heightPower lam (pair F G x b) = z := by
    rw [← heq, hK.heightPower_map_mul, heightPower, hK.height_of_mem hk, map_zero,
      Complex.exp_zero, mul_one]
  change ‖(Act a (h b)).val x‖ ≤ _
  rw [hd, hz, norm_mul, mul_comm ‖z‖]
  exact mul_le_mul_of_nonneg_right ((hC ⟨k, hk, rfl⟩).trans (le_max_right _ _)) (norm_nonneg _)

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

/-- The height twist of an inducing function on a fixed archimedean slice. -/
def parameterTwistSlice (hH : hK.HasSmoothHeightPairings hsmooth)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : ∀ b, functionInfiniteSlice F G φ b ∈ S)
    (lam : ComplexCharacterParameter F P) (b : FinPts) : S :=
  mulSmoothSlices F G hsmooth ⟨functionInfiniteSlice F G φ b, hφ b⟩
    (hK.heightPowerSlice hsmooth hH lam b)

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
@[simp]
theorem parameterTwistSlice_apply (hH : hK.HasSmoothHeightPairings hsmooth)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : ∀ b, functionInfiniteSlice F G φ b ∈ S)
    (lam : ComplexCharacterParameter F P) (b : FinPts) (x : H) :
    (hK.parameterTwistSlice hsmooth hH φ hφ lam b).val x =
      hK.parameterTwist φ lam (pair F G x b) := rfl

include hmax in
/-- A common exponent for the inducing derivatives bounds the twisted derivatives
by the same power of the matrix height times the absolute value of the twist. -/
theorem exists_parameterTwist_derivative_bound (hH : hK.HasSmoothHeightPairings hsmooth)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : ∀ b, functionInfiniteSlice F G φ b ∈ S)
    (hN : 0 < N) (e : ℝ)
    (hg : ∀ a : U, ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a ⟨functionInfiniteSlice F G φ b, hφ b⟩).val x‖ ≤
        C * adelicHeight F G rho (pair F G x b) ^ e)
    (lam : ComplexCharacterParameter F P) (a : U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a
        (hK.parameterTwistSlice hsmooth hH φ hφ lam b)).val x‖ ≤
        C * (adelicHeight F G rho (pair F G x b) ^ e * ‖hK.heightPower lam (pair F G x b)‖) :=
  exists_enveloping_bound_mul F G hsmooth hcalc
    (fun b => ⟨functionInfiniteSlice F G φ b, hφ b⟩) (hK.heightPowerSlice hsmooth hH lam)
    (fun b x => adelicHeight F G rho (pair F G x b) ^ e)
    (fun b x => ‖hK.heightPower lam (pair F G x b)‖) hg
    (hK.exists_enveloping_heightPowerSlice_bound hmax hsmooth hcalc hH lam)
    (fun b x => Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hN (pair F G x b))) _) a

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact
