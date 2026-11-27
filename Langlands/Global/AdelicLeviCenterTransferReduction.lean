import Langlands.Global.AdelicLeviCenterTransferReductionStatement
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof
import Langlands.Global.AdelicEisensteinTwistGrowth
import Langlands.Global.AdelicArchimedeanCharacterLog

/-! # From the normalized Harish-Chandra congruence to the Levi transfer of the center -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.UniversalEnveloping

/-- A linear map intertwining two representations of an enveloping algebra on the
generators intertwines them on every element. -/
theorem intertwine_of_ι {R L V W : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (ρ₁ : UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R V)
    (ρ₂ : UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R W) (Φ : V →ₗ[R] W)
    (h : ∀ x : L, Φ ∘ₗ ρ₁ (UniversalEnvelopingAlgebra.ι R x) =
      ρ₂ (UniversalEnvelopingAlgebra.ι R x) ∘ₗ Φ)
    (u : UniversalEnvelopingAlgebra R L) : Φ ∘ₗ ρ₁ u = ρ₂ u ∘ₗ Φ := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := R) (UniversalEnvelopingAlgebra.ringCon R L) u
  change Φ ∘ₗ ρ₁ (UniversalEnvelopingAlgebra.mkAlgHom R L t) =
    ρ₂ (UniversalEnvelopingAlgebra.mkAlgHom R L t) ∘ₗ Φ
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    ext v
    simp
  | «ι» x => exact h x
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, ha, LinearMap.comp_assoc, hb, LinearMap.comp_assoc]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]

end Langlands.Algebra.UniversalEnveloping

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme
  Langlands.Algebra.UniversalEnveloping Langlands.Global.AdelicGroupPoints

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]

local notation "Ainf" => CommAlgCat.of F (InfiniteAdeleRing F)

section Operators

/-- Pullback of plot-smooth functions along the archimedean point map of a morphism of
group schemes. -/
def plotSmoothPullback {H G : GroupScheme (Spec (CommRingCat.of F))} (j : H ⟶ G) :
    InfinitePlotSmoothFunctions F G →ₗ[ℂ] InfinitePlotSmoothFunctions F H where
  toFun f := ⟨fun m => f.val (H.affinePointsTarget j Ainf m), by
    intro E _ _ M _ _ p hp
    exact f.property E M _ (hp.postcomp j.hom.hom)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem plotSmoothPullback_apply {H G : GroupScheme (Spec (CommRingCat.of F))} (j : H ⟶ G)
    (f : InfinitePlotSmoothFunctions F G) (m : InfiniteAdelicGroupPoints F H) :
    (plotSmoothPullback j f).val m = f.val (H.affinePointsTarget j Ainf m) := rfl

/-- Right translation of plot-smooth functions on `G(F_∞)`. -/
def plotSmoothRightTranslation {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (g : InfiniteAdelicGroupPoints F G) :
    InfinitePlotSmoothFunctions F G →ₗ[ℂ] InfinitePlotSmoothFunctions F G where
  toFun f := ⟨fun x => f.val (x * g), by
    intro E _ _ M _ _ p hp
    exact f.property E M _ (CoordinateSmooth.mul G _ _ _ hp (coordinateSmooth_const G _ _ _ g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem plotSmoothRightTranslation_apply {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] (g : InfiniteAdelicGroupPoints F G) (f : InfinitePlotSmoothFunctions F G)
    (x : InfiniteAdelicGroupPoints F G) :
    (plotSmoothRightTranslation g f).val x = f.val (x * g) := rfl

/-- Multiplication of plot-smooth functions by a fixed plot-smooth function. -/
def plotSmoothMul {H : GroupScheme (Spec (CommRingCat.of F))} (χ : InfiniteAdelicGroupPoints F H → ℂ)
    (hχ : χ ∈ InfinitePlotSmoothFunctions F H) :
    InfinitePlotSmoothFunctions F H →ₗ[ℂ] InfinitePlotSmoothFunctions F H where
  toFun f := ⟨fun m => χ m * f.val m, by
    intro E _ _ M _ _ p hp
    exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
      ((hχ E M p hp).prodMk_space (f.property E M p hp))⟩
  map_add' f g := by
    apply Subtype.ext
    funext m
    change χ m * (f.val m + g.val m) = χ m * f.val m + χ m * g.val m
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext m
    change χ m * (c * f.val m) = c * (χ m * f.val m)
    ring

@[simp]
theorem plotSmoothMul_apply {H : GroupScheme (Spec (CommRingCat.of F))}
    (χ : InfiniteAdelicGroupPoints F H → ℂ) (hχ : χ ∈ InfinitePlotSmoothFunctions F H)
    (f : InfinitePlotSmoothFunctions F H) (m : InfiniteAdelicGroupPoints F H) :
    (plotSmoothMul χ hχ f).val m = χ m * f.val m := rfl

end Operators

section Intertwining

/-- Restriction along the point map of a morphism `j : H ⟶ G` carries the enveloping action of
`j_*(u)` on `G(F_∞)` to that of `u` on `H(F_∞)`. -/
theorem plotSmoothPullback_envelopingAction {H G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] [IsAffine G.X.left] {e d : ℕ}
    (hsmoothH : SmoothOfRelativeDimension e H.X.hom) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalcH : AdelicDifferentialCommutator F H hsmoothH)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (j : H ⟶ G)
    (u : AdelicEnvelopingAlgebra F H hsmoothH) :
    plotSmoothPullback j ∘ₗ
        plotSmoothEnvelopingAction F G hsmooth hcalc (pointEnvelopingMap F hsmoothH hsmooth j u) =
      plotSmoothEnvelopingAction F H hsmoothH hcalcH u ∘ₗ plotSmoothPullback j := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F H hsmoothH
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F H hsmoothH
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  refine intertwine_of_ι ((plotSmoothEnvelopingAction F G hsmooth hcalc).comp
    (pointEnvelopingMap F hsmoothH hsmooth j)) (plotSmoothEnvelopingAction F H hsmoothH hcalcH)
    (plotSmoothPullback j) (fun x => ?_) u
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [AlgHom.comp_apply, pointEnvelopingMap_ι_tmul, plotSmoothEnvelopingAction_generator,
      plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul,
      complexPlotSmoothLieAction_tmul]
    ext f m
    change z * groupDirectionalValue 𝓘(ℝ, smoothModel F d) (pointTangent F hsmoothH hsmooth j X)
        f.val (H.affinePointsTarget j Ainf m) =
      z * groupDirectionalValue 𝓘(ℝ, smoothModel F e) X
        (fun x => f.val (H.affinePointsTarget j Ainf x)) m
    rw [groupDirectionalValue_comp_hom 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
      (H.affinePointsTarget j Ainf) (contMDiff_affinePointsTarget F hsmoothH hsmooth j) X
      ((isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property) m]
    rfl
  | add x y hx hy =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]

/-- Right translation by `g` carries the enveloping action of `u` to that of `Ad(g) u`. -/
theorem plotSmoothRightTranslation_envelopingAction {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (g : InfiniteAdelicGroupPoints F G)
    (u : AdelicEnvelopingAlgebra F G hsmooth) :
    plotSmoothRightTranslation g ∘ₗ plotSmoothEnvelopingAction F G hsmooth hcalc u =
      plotSmoothEnvelopingAction F G hsmooth hcalc (adelicEnvelopingConjugation F G hsmooth g u) ∘ₗ
        plotSmoothRightTranslation g := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  refine intertwine_of_ι (plotSmoothEnvelopingAction F G hsmooth hcalc)
    ((plotSmoothEnvelopingAction F G hsmooth hcalc).comp (adelicEnvelopingConjugation F G hsmooth g))
    (plotSmoothRightTranslation g) (fun x => ?_) u
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [AlgHom.comp_apply, adelicEnvelopingConjugation_ι_tmul, plotSmoothEnvelopingAction_generator,
      plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul,
      complexPlotSmoothLieAction_tmul]
    ext f x
    change z * groupDirectionalValue 𝓘(ℝ, smoothModel F d) X f.val (x * g) =
      z * groupDirectionalValue 𝓘(ℝ, smoothModel F d) (adelicTangentConjugation F G hsmooth g X)
        (fun y => f.val (y * g)) x
    rw [groupDirectionalValue_rightTranslation 𝓘(ℝ, smoothModel F d) g X
      ((isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property) x]
    rfl
  | add x y hx hy =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]

/-- Multiplication by a smooth multiplicative function `χ` carries the enveloping action of the
shifted element `τ_χ(u)` to that of `u`. -/
theorem plotSmoothMul_envelopingAction {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] {e : ℕ} (hsmoothH : SmoothOfRelativeDimension e H.X.hom)
    (hcalcH : AdelicDifferentialCommutator F H hsmoothH) (χ : InfiniteAdelicGroupPoints F H → ℂ)
    (hχ : χ ∈ InfinitePlotSmoothFunctions F H) (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hlie : letI := fun v : NumberField.InfinitePlace F =>
        InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      letI := smoothLieGroup F H hsmoothH
      letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
        (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
      ∀ X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H),
        identityDerivative F hsmoothH χ ⁅X, Y⁆ = 0)
    (u : AdelicEnvelopingAlgebra F H hsmoothH) :
    plotSmoothMul χ hχ ∘ₗ
        plotSmoothEnvelopingAction F H hsmoothH hcalcH (envelopingCharacterShift F hsmoothH χ hlie u) =
      plotSmoothEnvelopingAction F H hsmoothH hcalcH u ∘ₗ plotSmoothMul χ hχ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F H hsmoothH
  let := smoothLieGroup F H hsmoothH
  let : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  have hχs : ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, ℂ) ∞ χ :=
    (isPlotSmooth_iff_contMDiff F H hsmoothH χ).mp hχ
  refine intertwine_of_ι ((plotSmoothEnvelopingAction F H hsmoothH hcalcH).comp
    (envelopingCharacterShift F hsmoothH χ hlie)) (plotSmoothEnvelopingAction F H hsmoothH hcalcH)
    (plotSmoothMul χ hχ) (fun x => ?_) u
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [AlgHom.comp_apply]
    change plotSmoothMul χ hχ ∘ₗ plotSmoothEnvelopingAction F H hsmoothH hcalcH
        (Langlands.Algebra.ComplexLieExtension.characterShift (identityDerivative F hsmoothH χ) hlie
          (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X))) = _
    rw [Langlands.Algebra.ComplexLieExtension.characterShift_ι, map_add, AlgHom.commutes,
      plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul]
    ext f m
    have hf : ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, ℂ) ∞ f.val :=
      (isPlotSmooth_iff_contMDiff F H hsmoothH f.val).mp f.property
    have hL : ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F e) ∞
        (fun y : InfiniteAdelicGroupPoints F H => m * y) := contMDiff_const.mul contMDiff_id
    have hp : MDifferentiableAt 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, ℂ) (fun y => χ (m * y)) 1 :=
      (hχs.comp hL).mdifferentiableAt (by simp)
    have hq : MDifferentiableAt 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, ℂ) (fun y => f.val (m * y)) 1 :=
      (hf.comp hL).mdifferentiableAt (by simp)
    have hD : mvfderiv 𝓘(ℝ, smoothModel F e) ((fun y => χ (m * y)) * fun y => f.val (m * y)) 1 =
        χ (m * 1) • mvfderiv 𝓘(ℝ, smoothModel F e) (fun y => f.val (m * y)) 1 +
          f.val (m * 1) • mvfderiv 𝓘(ℝ, smoothModel F e) (fun y => χ (m * y)) 1 :=
      (hp.hasMFDerivAt.mul hq.hasMFDerivAt).mfderiv
    have hc := groupDirectionalValue_character 𝓘(ℝ, smoothModel F e) hmul hχs X m
    change χ m * (z * groupDirectionalValue 𝓘(ℝ, smoothModel F e) X f.val m +
        Langlands.Algebra.ComplexLieExtension.linear (identityDerivative F hsmoothH χ)
          (z ⊗ₜ[ℝ] X) * f.val m) =
      z * mvfderiv 𝓘(ℝ, smoothModel F e) ((fun y => χ (m * y)) * fun y => f.val (m * y)) 1 X
    rw [hD]
    simp only [add_apply, smul_apply, smul_eq_mul,
      mul_one, Langlands.Algebra.ComplexLieExtension.linear_tmul]
    change χ m * (z * groupDirectionalValue 𝓘(ℝ, smoothModel F e) X f.val m +
        z * mvfderiv 𝓘(ℝ, smoothModel F e) χ 1 X * f.val m) =
      z * (χ m * groupDirectionalValue 𝓘(ℝ, smoothModel F e) X f.val m +
        f.val m * groupDirectionalValue 𝓘(ℝ, smoothModel F e) X χ m)
    rw [hc]
    ring
  | add x y hx hy =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]

/-- An element of the curve right ideal of `S` kills, at every point normalizing `S`, the
derivatives of a function that is left invariant under `S`. -/
theorem envelopingAction_apply_eq_zero_of_mem_curveRightIdeal
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (S : Set (InfiniteAdelicGroupPoints F G)) (f : InfinitePlotSmoothFunctions F G)
    (hf : ∀ s ∈ S, ∀ x, f.val (s * x) = f.val x) (x₀ : InfiniteAdelicGroupPoints F G)
    (hx₀ : ∀ s ∈ S, x₀ * s * x₀⁻¹ ∈ S) {w : AdelicEnvelopingAlgebra F G hsmooth}
    (hw : w ∈ curveRightIdeal F hsmooth S) :
    (plotSmoothEnvelopingAction F G hsmooth hcalc w f).val x₀ = 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨X, ⟨c, hc, hc0, hcS, hcX⟩, b, rfl⟩ := hw
    set φ := plotSmoothEnvelopingAction F G hsmooth hcalc b f with hφdef
    have hinv : ∀ s ∈ S, ∀ x, φ.val (s * x) = φ.val x := by
      intro s hs x
      have hfix : plotSmoothLeftTranslation F G s f = f :=
        Subtype.ext (funext fun y => hf s hs y)
      have h := congrArg (fun k : InfinitePlotSmoothFunctions F G => k.val x)
        (plotSmoothEnvelopingAction_leftTranslate F G hsmooth hcalc s b f)
      simp only [hfix, plotSmoothLeftTranslation_apply] at h
      exact h.symm
    have hφs : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ φ.val :=
      (isPlotSmooth_iff_contMDiff F G hsmooth φ.val).mp φ.property
    rw [map_mul, Module.End.mul_apply, plotSmoothEnvelopingAction_real_generator,
      plotSmoothDifferential_apply, ← hφdef]
    have hk : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
        (fun h : InfiniteAdelicGroupPoints F G => φ.val (x₀ * h)) :=
      hφs.comp (contMDiff_const.mul contMDiff_id)
    have hconst : (fun h : InfiniteAdelicGroupPoints F G => φ.val (x₀ * h)) ∘ c =
        fun _ => φ.val x₀ := by
      funext t
      simp only [Function.comp_apply]
      rw [show x₀ * c t = (x₀ * c t * x₀⁻¹) * x₀ by group]
      exact hinv _ (hx₀ _ (hcS t)) x₀
    rw [← hcX, ← mvfderiv_comp_apply_of_eq (0 : ℝ) (hk.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) hc0, hconst, mvfderiv_const]
    rfl
  | zero => rw [map_zero]; rfl
  | add a b _ _ ha hb =>
    rw [map_add, LinearMap.add_apply]
    change (plotSmoothEnvelopingAction F G hsmooth hcalc a f).val x₀ +
      (plotSmoothEnvelopingAction F G hsmooth hcalc b f).val x₀ = 0
    rw [ha, hb, add_zero]
  | smul r a _ ha =>
    rw [map_smul, LinearMap.smul_apply]
    change r * (plotSmoothEnvelopingAction F G hsmooth hcalc a f).val x₀ = 0
    rw [ha, mul_zero]

end Intertwining

section Clause

omit [NumberField F] in
/-- If the image of `W` is normal in `R`, then for `ι = k ≫ r` the points `ι(m)` normalize the
image of `W(F_∞)` in `G(F_∞)`. -/
theorem affinePointsTarget_conj_mem_range {G R W H : GroupScheme (Spec (CommRingCat.of F))}
    (r : R ⟶ G) (iW : W ⟶ R) (hN : (SubgroupFunctor.range iW).IsNormal) (k : H ⟶ R)
    (m : InfiniteAdelicGroupPoints F H) :
    ∀ s ∈ Set.range (W.affinePointsTarget (iW ≫ r) Ainf),
      H.affinePointsTarget (k ≫ r) Ainf m * s * (H.affinePointsTarget (k ≫ r) Ainf m)⁻¹ ∈
        Set.range (W.affinePointsTarget (iW ≫ r) Ainf) := by
  rintro _ ⟨w, rfl⟩
  let a : R.affinePoints Ainf := H.affinePointsTarget k Ainf m
  obtain ⟨w', hw'⟩ := hN _ a (W.affinePointsTarget iW Ainf w) trivial ⟨w, rfl⟩
  refine ⟨w', ?_⟩
  have h1 : H.affinePointsTarget (k ≫ r) Ainf m = R.affinePointsTarget r Ainf a := rfl
  have h2 : W.affinePointsTarget (iW ≫ r) Ainf w =
      R.affinePointsTarget r Ainf (W.affinePointsTarget iW Ainf w) := rfl
  have h3 : W.affinePointsTarget (iW ≫ r) Ainf w' =
      R.affinePointsTarget r Ainf (W.affinePointsTarget iW Ainf w') := rfl
  rw [h1, h2, h3, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (R.affinePointsTarget r Ainf) hw'

/-- One clause of the Levi transfer, from the normalized congruence: for a Levi map `k : H ⟶ R`
into a group `R ⟶ G` normalizing `W`, the normalized restrictions of left `W(F_∞)`-invariant
functions transform under `y` as under `z`. -/
theorem levi_clause_of_congruence {G R W H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine H.X.left] {d e : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hsmoothH : SmoothOfRelativeDimension e H.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hcalcH : AdelicDifferentialCommutator F H hsmoothH) (hG : IsConnectedReductive G)
    (r : R ⟶ G) (iW : W ⟶ R) (hN : (SubgroupFunctor.range iW).IsNormal) (k : H ⟶ R)
    (i : H ⟶ G) (hi : i = k ≫ r)
    (χ : InfiniteAdelicGroupPoints F H → ℂ) (hχ : χ ∈ InfinitePlotSmoothFunctions F H)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hlie : letI := fun v : NumberField.InfinitePlace F =>
        InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      letI := smoothLieGroup F H hsmoothH
      letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
        (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
      ∀ X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H),
        identityDerivative F hsmoothH χ ⁅X, Y⁆ = 0)
    (z : AdelicEnvelopingCenter F G hsmooth) (y : AdelicEnvelopingAlgebra F H hsmoothH)
    (hy : (z : AdelicEnvelopingAlgebra F G hsmooth) -
        pointEnvelopingMap F hsmoothH hsmooth i (envelopingCharacterShift F hsmoothH χ hlie y) ∈
      curveRightIdeal F hsmooth (Set.range (W.affinePointsTarget (iW ≫ r) Ainf)))
    (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : f ∈ InfinitePlotSmoothFunctions F G)
    (hinv : ∀ (w : InfiniteAdelicGroupPoints F W) (x : InfiniteAdelicGroupPoints F G),
      f (W.affinePointsTarget (iW ≫ r) Ainf w * x) = f x)
    (g : InfiniteAdelicGroupPoints F G)
    (h : (fun m => χ m * f (H.affinePointsTarget i Ainf m * g)) ∈
      InfinitePlotSmoothFunctions F H) :
    ((plotSmoothEnvelopingAction F H hsmoothH hcalcH y) ⟨_, h⟩ :
        InfiniteAdelicGroupPoints F H → ℂ) =
      fun m => χ m * (plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ :
        InfiniteAdelicGroupPoints F G → ℂ) (H.affinePointsTarget i Ainf m * g) := by
  subst hi
  let F0 : InfinitePlotSmoothFunctions F G := ⟨f, hf⟩
  let Fg := plotSmoothRightTranslation g F0
  let ψ := plotSmoothPullback (k ≫ r) Fg
  let τy := envelopingCharacterShift F hsmoothH χ hlie y
  let jτy := pointEnvelopingMap F hsmoothH hsmooth (k ≫ r) τy
  have hψ : (⟨_, h⟩ : InfinitePlotSmoothFunctions F H) = plotSmoothMul χ hχ ψ := rfl
  have hB := congrArg (fun T => T ψ)
    (plotSmoothMul_envelopingAction hsmoothH hcalcH χ hχ hmul hlie y)
  have hA := congrArg (fun T => T Fg)
    (plotSmoothPullback_envelopingAction hsmoothH hsmooth hcalcH hcalc (k ≫ r) τy)
  have hD := congrArg (fun T => T F0)
    (plotSmoothRightTranslation_envelopingAction hsmooth hcalc g z.val)
  simp only [LinearMap.comp_apply] at hA hB hD
  rw [adelicEnvelopingCenterConjugation F G hsmooth hG g z.val z.property] at hD
  rw [hψ, ← hB]
  funext m
  change χ m * (plotSmoothEnvelopingAction F H hsmoothH hcalcH τy ψ).val m = _
  rw [← hA]
  change χ m * (plotSmoothEnvelopingAction F G hsmooth hcalc jτy Fg).val
      (H.affinePointsTarget (k ≫ r) Ainf m) = _
  have hsplit : jτy = z.val - (z.val - jτy) := by abel
  rw [hsplit, map_sub, LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply,
    envelopingAction_apply_eq_zero_of_mem_curveRightIdeal hsmooth hcalc _ Fg
      (by rintro _ ⟨w, rfl⟩ x; change f (_ * x * g) = f (x * g); rw [mul_assoc]; exact hinv w (x * g))
      _ (affinePointsTarget_conj_mem_range r iW hN k m) hy, sub_zero, ← hD]
  rfl

end Clause

section Normalizer

/-- On `G(F_∞)`, `m ↦ j(m)^λ` is smooth for a morphism `j : G ⟶ H` and a complex character
parameter `λ` of `H`. -/
theorem contMDiff_parameterPower_map_ofInfinite {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (j : G ⟶ H)
    (lam : ComplexCharacterParameter F H) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun m => parameterPower F H lam (AdelicGroupPoints.map F G H j (ofInfinite F G m))) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have hlog (ψ : rationalCharacters G) : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ) ∞
      (fun m => AdelicGroupPoints.characterLog F G (ofInfinite F G m) ψ) := by
    intro m
    have hm := AdelicGroupPoints.contMDiffAt_archimedeanLogRegular F G hsmooth
      (AdelicGroupPoints.characterRegularFunction F G ψ) m (fun v => by
        rw [← AdelicGroupPoints.characterUnits_val_eq_evaluation]
        exact Units.ne_zero (Units.map (Pi.evalMonoidHom _ v)
          (AdelicGroupPoints.characterUnits F G ψ.toMul Ainf m)))
    refine hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    change AdelicGroupPoints.characterLog F G (ofInfinite F G y) ψ = _
    rw [AdelicGroupPoints.characterLog_apply_ofInfinite]
    rfl
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    have hexp : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (s * (t : ℂ))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
    refine (hexp.contMDiff.comp (hlog (characterRestrict j χ))).congr fun m => ?_
    simp only [Function.comp_apply, parameterPower, AdelicGroupPoints.characterLog_map,
      complexParameterPairing_tmul]
    rfl
  | add a b ha hb =>
    have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_mul
    refine (hmul.contMDiff.comp (ha.prodMk_space hb)).congr fun x => ?_
    simp only [Function.comp_apply, parameterPower, map_add, LinearMap.add_apply,
      Complex.exp_add]

/-- `m ↦ j(m)^λ` is multiplicative on `G(F_∞)`. -/
theorem parameterPower_map_ofInfinite_mul {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] (j : G ⟶ H) (lam : ComplexCharacterParameter F H)
    (x y : InfiniteAdelicGroupPoints F G) :
    parameterPower F H lam (AdelicGroupPoints.map F G H j (ofInfinite F G (x * y))) =
      parameterPower F H lam (AdelicGroupPoints.map F G H j (ofInfinite F G x)) *
        parameterPower F H lam (AdelicGroupPoints.map F G H j (ofInfinite F G y)) := by
  rw [map_mul, map_mul, ← parameterCharacter_apply, map_mul, Units.val_mul,
    parameterCharacter_apply, parameterCharacter_apply]

end Normalizer



end Langlands.Global.InfiniteAdelicGroupPoints

namespace Langlands.Global

open Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme
  AdelicGroupPoints InfiniteAdelicGroupPoints

attribute [local instance 100] LieRing.ofAssociativeRing

section Reduction

/-- The normalized Harish-Chandra congruence gives the Levi transfer of the center. -/
theorem leviRestrictionCenterTransfer_of_congruence :
    LeviRestrictionCenterCongruenceStatement.{u} → LeviRestrictionCenterTransferStatement.{u} := by
  intro hcong F _ _ G P M U Q M' V _ _ _ _ _ _ p iU l q iV l' w c hG hp hU hl hq hV hl' hw
    d d' hsmooth hcalc hsmooth' hcalc' z Ainf ιQ ιP δQ δP
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F M' hsmooth'
  let := smoothLieGroup F M' hsmooth'
  let : LieGroup 𝓘(ℝ, smoothModel F d') (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F M') := LieGroup.of_le (n := ∞) (by simp)
  have hδQs : ContMDiff 𝓘(ℝ, smoothModel F d') 𝓘(ℝ, ℂ) ∞ δQ :=
    contMDiff_parameterPower_map_ofInfinite hsmooth' l' _
  have hδPs : ContMDiff 𝓘(ℝ, smoothModel F d') 𝓘(ℝ, ℂ) ∞ δP :=
    contMDiff_parameterPower_map_ofInfinite hsmooth' (c ≫ l) _
  have hδQ : δQ ∈ InfinitePlotSmoothFunctions F M' :=
    (isPlotSmooth_iff_contMDiff F M' hsmooth' δQ).mpr hδQs
  have hδP : δP ∈ InfinitePlotSmoothFunctions F M' :=
    (isPlotSmooth_iff_contMDiff F M' hsmooth' δP).mpr hδPs
  have hmulQ : ∀ x y, δQ (x * y) = δQ x * δQ y := parameterPower_map_ofInfinite_mul l' _
  have hmulP : ∀ x y, δP (x * y) = δP x * δP y := parameterPower_map_ofInfinite_mul (c ≫ l) _
  have hQlie : ∀ X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F d') (InfiniteAdelicGroupPoints F M'),
      identityDerivative F hsmooth' δQ ⁅X, Y⁆ = 0 := fun X Y =>
    mvfderiv_character_lie 𝓘(ℝ, smoothModel F d') hmulQ hδQs X Y
  have hPlie : ∀ X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F d') (InfiniteAdelicGroupPoints F M'),
      identityDerivative F hsmooth' δP ⁅X, Y⁆ = 0 := fun X Y =>
    mvfderiv_character_lie 𝓘(ℝ, smoothModel F d') hmulP hδPs X Y
  obtain ⟨y, hyQ, hyP⟩ := hcong F G P M U Q M' V p iU l q iV l' w c hG hp hU hl hq hV hl' hw
    hsmooth hsmooth' z hQlie hPlie
  refine ⟨y, ?_, ?_⟩
  · intro f hf hinv g h
    exact levi_clause_of_congruence hsmooth hsmooth' hcalc hcalc' hG q iV hV.1.isNormal l'
      (l' ≫ q) rfl δQ hδQ hmulQ hQlie z y hyQ f hf hinv g h
  · intro f hf hinv g h
    exact levi_clause_of_congruence hsmooth hsmooth' hcalc hcalc' hG p iU hU.1.isNormal (c ≫ l)
      (c ≫ l ≫ p) (Category.assoc c l p).symm δP hδP hmulP hPlie z y hyP f hf hinv g h

/-- Proof of `LeviRestrictionCenterTransferReductionStatement`. -/
theorem leviRestrictionCenterTransferReduction :
    LeviRestrictionCenterTransferReductionStatement.{u} :=
  leviRestrictionCenterTransfer_of_congruence

end Reduction

end Langlands.Global
