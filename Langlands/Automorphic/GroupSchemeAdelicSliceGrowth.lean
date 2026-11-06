import Langlands.Automorphic.GroupSchemeAdelicGrowth
import Langlands.Automorphic.GroupSchemeGrowth
import Langlands.Global.FiniteAdelicGroupCompactOpen

/-! # Full adelic growth restricts to the original archimedean slices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped Classical CategoryTheory.MonObj Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicMatrixHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private theorem completion_norm_le_mixed (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  by_cases hv : v.IsReal
  · calc
      ‖x v‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v)‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
          (map_zero _) _).symm
      _ ≤ ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F x).1‖ :=
        norm_le_pi_norm (InfiniteAdeleRing.ringEquiv_mixedSpace F x).1
          (⟨v, hv⟩ : {w : InfinitePlace F // w.IsReal})
      _ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := norm_fst_le _
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    calc
      ‖x v‖ = ‖InfinitePlace.Completion.extensionEmbedding v (x v)‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
          (map_zero _) _).symm
      _ ≤ ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F x).2‖ :=
        norm_le_pi_norm (InfiniteAdeleRing.ringEquiv_mixedSpace F x).2
          (⟨v, hc⟩ : {w : InfinitePlace F // w.IsComplex})
      _ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := norm_snd_le _

private theorem entry_norm_le_operatorNorm
    (A : ArchimedeanMatrix F n) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast (show ‖A i j‖₊ ≤ Finset.univ.sup (fun k : Fin n => ∑ l : Fin n, ‖A k l‖₊) from
    (Finset.single_le_sum (fun l _ => (show 0 ≤ ‖A i l‖₊ from zero_le))
      (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k : Fin n => ∑ l : Fin n, ‖A k l‖₊) (Finset.mem_univ i)))

/-- Each unnormalized infinite-place maximum is bounded by the original mixed matrix height. -/
theorem infiniteLocal_le_matrixHeight (g : AdelicGL F n) (v : InfinitePlace F) :
    infiniteLocal F n g v ≤ ArchimedeanGL.matrixHeight F n (AdelicGL.infinite F n g) := by
  have hentry (h : AdelicGL F n) (i j : Fin n) :
      ‖infiniteProjection F v (h i j)‖ ≤
        ‖(archimedeanGLCoordinates F n (AdelicGL.infinite F n h)).val‖ := by
    change ‖(h i j).1 v‖ ≤
      ‖(archimedeanGLCoordinates F n (AdelicGL.infinite F n h)).val‖
    calc
      _ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (h i j).1‖ :=
        completion_norm_le_mixed F (h i j).1 v
      _ ≤ _ := entry_norm_le_operatorNorm F n
        (archimedeanGLCoordinates F n (AdelicGL.infinite F n h)).val i j
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (ArchimedeanGL.matrixHeight_nonneg F n _)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (ArchimedeanGL.matrixHeight_nonneg F n _)).mpr
    intro j
    exact (hentry g i j).trans (ArchimedeanGL.norm_val_le_matrixHeight F n _)
  · apply (pi_norm_le_iff_of_nonneg (ArchimedeanGL.matrixHeight_nonneg F n _)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (ArchimedeanGL.matrixHeight_nonneg F n _)).mpr
    intro j
    have h := (hentry g⁻¹ i j).trans
      (ArchimedeanGL.norm_val_le_matrixHeight F n (AdelicGL.infinite F n g⁻¹))
    simpa only [map_inv, ArchimedeanGL.matrixHeight_inv] using h

/-- The fixed finite-place factor and dimension scalar for one finite matrix slice. -/
def sliceHeightConstant (b : FiniteAdelicGL F n) : ℝ :=
  (n : ℝ) ^ (∑ v : InfinitePlace F, v.mult) *
    ∏ᶠ v : FinitePlace F, finiteLocal F n (AdelicGL.pair F n 1 b) v

theorem sliceHeightConstant_nonneg (b : FiniteAdelicGL F n) :
    0 ≤ sliceHeightConstant F n b :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (finprod_nonneg fun _v => MatrixInverseHeight.localMaximum_nonneg _ _)

/-- On a fixed finite slice, the full height has an explicit archimedean polynomial bound. -/
theorem height_pair_le (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    height F n (AdelicGL.pair F n a b) ≤ sliceHeightConstant F n b *
      ArchimedeanGL.matrixHeight F n a ^ (∑ v : InfinitePlace F, v.mult) := by
  have hlocal (v : InfinitePlace F) :
      (n : ℝ) * infiniteLocal F n (AdelicGL.pair F n a b) v ≤
        n * ArchimedeanGL.matrixHeight F n a := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa only [AdelicGL.infinite_pair] using
      infiniteLocal_le_matrixHeight F n (AdelicGL.pair F n a b) v
  have hprod := Finset.prod_le_prod₀
    (f := fun v : InfinitePlace F =>
      ((n : ℝ) * infiniteLocal F n (AdelicGL.pair F n a b) v) ^ v.mult)
    (g := fun v : InfinitePlace F => ((n : ℝ) * ArchimedeanGL.matrixHeight F n a) ^ v.mult)
    (s := Finset.univ)
    (fun v _ => pow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (MatrixInverseHeight.localMaximum_nonneg _ _)) _)
    (fun v _ => pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _) (MatrixInverseHeight.localMaximum_nonneg _ _))
      (hlocal v) _)
  have hfinite : (fun v : FinitePlace F => finiteLocal F n (AdelicGL.pair F n a b) v) =
      (fun v : FinitePlace F => finiteLocal F n (AdelicGL.pair F n 1 b) v) := rfl
  unfold height
  rw [hfinite]
  calc
    _ ≤ (∏ v : InfinitePlace F, ((n : ℝ) * ArchimedeanGL.matrixHeight F n a) ^ v.mult) *
        ∏ᶠ v : FinitePlace F, finiteLocal F n (AdelicGL.pair F n 1 b) v :=
      mul_le_mul_of_nonneg_right hprod
        (finprod_nonneg fun v => MatrixInverseHeight.localMaximum_nonneg _ _)
    _ = _ := by
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        sliceHeightConstant]
      ring

end Langlands.Global.AdelicMatrixHeight

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

variable [IsAffine G.X.left]

set_option maxHeartbeats 1600000 in
/-- Infinite coefficient projection commutes with evaluation of the representation. -/
theorem infiniteMatrix_infinite (g : AdelicGroupPoints F G) :
    infiniteMatrix F G rho (AdelicGroupPoints.infinite F G g) =
      AdelicGL.infinite F N (adelicMatrix F G rho g) :=
  rho.affineMatrix_naturality
    (S := CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (T := CommAlgCat.of F (InfiniteAdeleRing F))
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) g

set_option maxHeartbeats 1600000 in
/-- Finite coefficient projection commutes with evaluation of the representation. -/
theorem finiteMatrix_finite (g : AdelicGroupPoints F G) :
    finiteMatrix F G rho (AdelicGroupPoints.finite F G g) =
      AdelicGL.finite F N (adelicMatrix F G rho g) :=
  rho.affineMatrix_naturality
    (S := CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (T := CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) g

/-- Actual point pairing becomes the original entrywise matrix pairing. -/
theorem adelicMatrix_pair (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) :
    adelicMatrix F G rho (AdelicGroupPoints.pair F G a b) =
      AdelicGL.pair F N (infiniteMatrix F G rho a) (finiteMatrix F G rho b) := by
  apply (AdelicGL.split F N).injective
  change (AdelicGL.infinite F N _, AdelicGL.finite F N _) =
    (AdelicGL.infinite F N _, AdelicGL.finite F N _)
  rw [← infiniteMatrix_infinite, ← finiteMatrix_finite,
    AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair,
    AdelicGL.infinite_pair, AdelicGL.finite_pair]

/-- Full representation height on a fixed finite slice has an archimedean polynomial bound. -/
theorem adelicHeight_pair_le (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) :
    adelicHeight F G rho (AdelicGroupPoints.pair F G a b) ≤
      AdelicMatrixHeight.sliceHeightConstant F N (finiteMatrix F G rho b) *
        height F G rho a ^ (∑ v : InfinitePlace F, v.mult) := by
  unfold adelicHeight
  rw [adelicMatrix_pair]
  exact AdelicMatrixHeight.height_pair_le F N _ _

end Langlands.Global.RepresentationGrowth

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- A full adelic polynomial bound supplies the existing bound on every finite slice. -/
theorem HasAdelicPolynomialGrowth.polynomialGrowth (hN : 0 < N)
    {f : ContinuousRationalFunctions F G} (hf : HasAdelicPolynomialGrowth F G rho f) :
    HasPolynomialGrowth F G rho f := by
  obtain ⟨C, hC, d, hf⟩ := hf
  intro b
  let B := AdelicMatrixHeight.sliceHeightConstant F N
    (RepresentationGrowth.finiteMatrix F G rho b)
  have hB : 0 ≤ B := AdelicMatrixHeight.sliceHeightConstant_nonneg F N _
  refine ⟨C * B ^ d, mul_nonneg hC (pow_nonneg hB d),
    (∑ v : NumberField.InfinitePlace F, v.mult) * d, fun a => ?_⟩
  calc
    ‖infiniteSlice F G b f a‖ ≤
        C * RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.pair F G a b) ^ d :=
      hf _
    _ ≤ C * (B * RepresentationGrowth.height F G rho a ^
        (∑ v : NumberField.InfinitePlace F, v.mult)) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN _))
          (RepresentationGrowth.adelicHeight_pair_le F G rho a b) d) hC
    _ = (C * B ^ d) * RepresentationGrowth.height F G rho a ^
        ((∑ v : NumberField.InfinitePlace F, v.mult) * d) := by rw [mul_pow, pow_mul]; ring

/-- The real-exponent source-norm condition also supplies every original slice bound. -/
theorem HasAdelicModerateGrowth.polynomialGrowth (hN : 0 < N)
    {f : ContinuousRationalFunctions F G} (hf : HasAdelicModerateGrowth F G rho f) :
    HasPolynomialGrowth F G rho f :=
  ((hasAdelicModerateGrowth_iff F G rho hN f).mp hf).polynomialGrowth F G rho hN

/-- Inclusion of the unchanged full-growth functions into the slice-growth subrepresentation. -/
theorem adelicGrowth_le_polynomialGrowth (hN : 0 < N) :
    adelicGrowthSubrepresentation F G rho hN ≤ polynomialGrowthSubrepresentation F G rho := by
  intro f hf
  apply (mem_polynomialGrowthSubrepresentation F G rho f).mpr
  exact HasAdelicPolynomialGrowth.polynomialGrowth F G rho hN hf

/-- The same inclusion retains the existing common finite stabilizer and smooth slices. -/
theorem finitePlotSmoothAdelicGrowth_le_polynomialGrowth (hN : 0 < N) :
    finitePlotSmoothAdelicGrowthSubrepresentation F G rho hN ≤
      finitePlotSmoothPolynomialGrowthSubrepresentation F G rho :=
  inf_le_inf_left _ (adelicGrowth_le_polynomialGrowth F G rho hN)

section GeneralLinearComparison

variable (n : ℕ) (hn : 0 < n)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
local notation "std" => GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F)

local instance sliceGrowthGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- A genuine unchanged-function injection into the original matrix slice-growth space. -/
def adelicGrowthGeneralLinearMap :
    ↥(adelicGrowthSubrepresentation F GLG std hn).toSubmodule →ₗ[ℂ]
      Langlands.Automorphic.PolynomialGrowthRationalFunctions F n :=
  (polynomialGrowthGeneralLinearEquiv F n).toLinearMap.comp
    (Submodule.inclusion (adelicGrowth_le_polynomialGrowth F GLG std hn))

theorem adelicGrowthGeneralLinearMap_injective :
    Function.Injective (adelicGrowthGeneralLinearMap F n hn) :=
  (polynomialGrowthGeneralLinearEquiv F n).injective.comp (Submodule.inclusion_injective _)

@[simp] theorem adelicGrowthGeneralLinearMap_val
    (f : ↥(adelicGrowthSubrepresentation F GLG std hn).toSubmodule) :
    (adelicGrowthGeneralLinearMap F n hn f).val = continuousGeneralLinearEquiv F n f.val := rfl

/-- The injection intertwines the original full positive right translations. -/
theorem adelicGrowthGeneralLinearMap_rightAction
    (f : ↥(adelicGrowthSubrepresentation F GLG std hn).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    adelicGrowthGeneralLinearMap F n hn
        ((adelicGrowthSubrepresentation F GLG std hn).toRepresentation g f) =
      Langlands.Automorphic.polynomialGrowthRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (adelicGrowthGeneralLinearMap F n hn f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- A genuine injection into the original finite-smooth matrix growth intersection. -/
def finitePlotSmoothAdelicGrowthGeneralLinearMap :
    ↥(finitePlotSmoothAdelicGrowthSubrepresentation F GLG std hn).toSubmodule →ₗ[ℂ]
      ↥(Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n).toSubmodule :=
  (finitePlotSmoothPolynomialGrowthGeneralLinearEquiv F n).toLinearMap.comp
    (Submodule.inclusion (finitePlotSmoothAdelicGrowth_le_polynomialGrowth F GLG std hn))

theorem finitePlotSmoothAdelicGrowthGeneralLinearMap_injective :
    Function.Injective (finitePlotSmoothAdelicGrowthGeneralLinearMap F n hn) :=
  (finitePlotSmoothPolynomialGrowthGeneralLinearEquiv F n).injective.comp
    (Submodule.inclusion_injective _)

@[simp] theorem finitePlotSmoothAdelicGrowthGeneralLinearMap_val
    (f : ↥(finitePlotSmoothAdelicGrowthSubrepresentation F GLG std hn).toSubmodule) :
    (finitePlotSmoothAdelicGrowthGeneralLinearMap F n hn f).val =
      continuousGeneralLinearEquiv F n f.val := rfl

/-- The common-stabilizer injection also intertwines the unchanged full adelic action. -/
theorem finitePlotSmoothAdelicGrowthGeneralLinearMap_rightAction
    (f : ↥(finitePlotSmoothAdelicGrowthSubrepresentation F GLG std hn).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    finitePlotSmoothAdelicGrowthGeneralLinearMap F n hn
        ((finitePlotSmoothAdelicGrowthSubrepresentation F GLG std hn).toRepresentation g f) =
      (Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (finitePlotSmoothAdelicGrowthGeneralLinearMap F n hn f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

end GeneralLinearComparison

end Langlands.Automorphic.GroupSchemeFunctions
