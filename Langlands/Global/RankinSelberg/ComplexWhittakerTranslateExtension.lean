import Langlands.Global.RankinSelberg.ComplexWhittakerSmoothExtension

/-! # Exact Whittaker values of genuine translates under the smooth extension -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslateExtension

open Langlands.Archimedean (complexPositionCharacter continuous_unitary_toUnits matrixModel
  rightTranslation_mem_principalSeries unitaryCompact)
open Langlands.Archimedean.UnitaryFinitePolynomial (polynomialStar polynomialStar_toSubalgebra
  inv_mul_mem_separated separated)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCentralPolynomialWeight (complexCentralPolynomialWeight)
open ComplexCompactDifferenceDensity (convolution convolution_error)
open ComplexCompactDifferences (displacementProduct)
open ComplexCompactSmoothDifferences (compactFunctionDifference CompactProfileDifferenceBound)
open ComplexGodement (compactMatrixHaar)
open ComplexLocalWhittakerGrowth (complexWhittakerCompactProjection)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile finiteToSmooth
  exists_smooth_compact_difference_bound)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "U" => fun n => unitaryCompact ℂ n
local notation "Std" => Automorphic.complexStandardKFinite

local instance translateExtensionMatrixMeasurable (n : ℕ) : MeasurableSpace (K n) := borel _
local instance translateExtensionMatrixBorel (n : ℕ) : BorelSpace (K n) := ⟨rfl⟩

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- Right translation is defined on the full smooth standard module. -/
def smoothTranslate (g : G n) (F : SmoothStandard n ds) : SmoothStandard n ds :=
  ⟨Whittaker.rightTranslation ℂ (G n) g F.val,
    rightTranslation_mem_principalSeries (complexPositionCharacter ds) F.2 g⟩

@[simp]
theorem smoothTranslate_apply (g : G n) (F : SmoothStandard n ds) (x : G n) :
    (smoothTranslate g F).val x = F.val (x * g) := rfl

private def compactEquiv (n : ℕ) : K n ≃* U n where
  toFun k := ⟨Unitary.toUnits k, k.2⟩
  invFun k := ⟨k.val.val, k.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Units.ext rfl)
  map_mul' k l := Subtype.ext (Unitary.toUnits.map_mul k l)

private theorem continuous_compactEquiv (n : ℕ) : Continuous (compactEquiv n) :=
  continuous_unitary_toUnits.subtype_mk _

private theorem continuous_compactEquiv_symm (n : ℕ) : Continuous (compactEquiv n).symm :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

private theorem polynomial_finiteLeftSpan (w : C(K n, ℂ)) (hw : w ∈ polynomialStar n) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun x : K n => fun k => w (x⁻¹ * k))) := by
  have hw' : w ∈ (polynomialStar n).toSubalgebra := hw
  rw [polynomialStar_toSubalgebra] at hw'
  have hsep := inv_mul_mem_separated hw'
  rw [separated] at hsep
  obtain ⟨m, c, s, hs⟩ := Submodule.mem_span_set'.mp hsep
  choose α _ β hβ using fun i => (s i).property
  let β' (i : Fin m) : K n → ℂ := β i
  have hV : FiniteDimensional ℂ (Submodule.span ℂ (range β')) :=
    FiniteDimensional.span_of_finite ℂ (finite_range β')
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (range β'))
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  change (fun k => w (x⁻¹ * k)) ∈ Submodule.span ℂ (range β')
  have hrep : (fun k => w (x⁻¹ * k)) = ∑ i, (c i * α i x) • β' i := by
    funext k
    have hh := (congrFun (congrFun hs x) k).symm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh ⊢
    simp_rw [hβ, ← mul_assoc] at hh
    exact hh
  rw [hrep]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- An actual compact projection of a translate with a polynomial weight, written in
unitary matrix coordinates, is compatible with the exact Whittaker map. -/
theorem exists_polynomial_projection (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)) (hB : IsComplexWhittakerIntertwiner r ds a B)
    (w : C(K (r + 1), ℂ)) (hw : w ∈ polynomialStar (r + 1)) (f : Std (r + 1) ds) (g : G (r + 1)) :
    ∃ p : Std (r + 1) ds,
      (∀ x : G (r + 1), p.val x = ∫ k : K (r + 1), w k * f.val (x * Unitary.toUnits k * g)
        ∂compactMatrixHaar (r + 1)) ∧
      ∀ x : G (r + 1), B p x = ∫ k : K (r + 1), w k * B f (x * Unitary.toUnits k * g)
        ∂compactMatrixHaar (r + 1) := by
  let n := r + 1
  let e := compactEquiv n
  let μ := (compactMatrixHaar n).map e
  have he : Continuous e := continuous_compactEquiv n
  have hμ : μ.IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure (compactMatrixHaar n) e.toMonoidHom he e.surjective
  let w' : C(U n, ℂ) := ⟨fun k => w (e.symm k), w.continuous.comp (continuous_compactEquiv_symm n)⟩
  let W : Submodule ℂ (K n → ℂ) := Submodule.span ℂ (range fun x : K n => fun k => w (x⁻¹ * k))
  have hW : FiniteDimensional ℂ W := polynomial_finiteLeftSpan w hw
  let P : (K n → ℂ) →ₗ[ℂ] (U n → ℂ) := LinearMap.pi fun k => LinearMap.proj (e.symm k)
  have hFin : FiniteDimensional ℂ (Submodule.span ℂ (range fun x : U n => fun k => w' (x⁻¹ * k))) := by
    apply Submodule.finiteDimensional_of_le (S₂ := W.map P)
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    refine ⟨fun k => w ((e.symm x)⁻¹ * k), Submodule.subset_span ⟨e.symm x, rfl⟩, ?_⟩
    funext k
    change w ((e.symm x)⁻¹ * e.symm k) = w (e.symm (x⁻¹ * k))
    rw [map_mul e.symm, map_inv e.symm]
  obtain ⟨p, hp, hBp⟩ := complexWhittakerCompactProjection (r := r) ds a μ hμ w' hFin B hB f g
  have transport {F : G n → ℂ} (hF : Continuous F) (x : G n) :
      (∫ k : U n, w' k * F (x * k.val * g) ∂μ) =
        ∫ k : K n, w k * F (x * Unitary.toUnits k * g) ∂compactMatrixHaar n := by
    have hc : Continuous (fun k : U n => w' k * F (x * k.val * g)) := w'.continuous.mul
      (hF.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    rw [integral_map he.measurable.aemeasurable hc.aestronglyMeasurable]
    apply integral_congr_ae (ae_of_all _ fun k => ?_)
    change w (e.symm (e k)) * F (x * Unitary.toUnits k * g) = _
    rw [e.symm_apply_apply]
  exact ⟨p, fun x => (hp x).trans (transport f.2.1.1.continuous x),
    fun x => (hBp x).trans (transport (hB.2.1 f).continuous x)⟩

/-- Any finite-order extension of exact identity evaluation gives the original Whittaker
function when evaluated on genuine right translates of compact-finite vectors. -/
def ComplexWhittakerTranslateExtensionStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∀ (L : SmoothStandard (r + 1) ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ), 0 ≤ C →
    (∀ f : Std (r + 1) ds, L (finiteToSmooth f) = B f 1) →
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) →
    ∀ (f : Std (r + 1) ds) (g : G (r + 1)), L (smoothTranslate g (finiteToSmooth f)) = B f g

set_option maxHeartbeats 850000 in
theorem complexWhittakerTranslateExtension : ComplexWhittakerTranslateExtensionStatement := by
  intro r ds a B hB L J C hC hRestr hBound f g
  let n := r + 1
  let F := smoothTranslate g (finiteToSmooth f)
  let φ : K n → ℂ := compactProfile F
  let G₀ : G n → ℂ := fun x => B f (x * g)
  let ψ (x : K n) := G₀ (Unitary.toUnits x)
  have hG₀ : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ G₀ := (hB.2.1 f).comp contMDiff_mul_right
  have hφ : Continuous φ := F.2.1.continuous.comp continuous_unitary_toUnits
  have hψ : Continuous ψ := hG₀.continuous.comp continuous_unitary_toUnits
  obtain ⟨D, hD, hDφ⟩ := exists_smooth_compact_difference_bound F.2.1 (J + 1)
  obtain ⟨E, hE, hEψ⟩ := exists_smooth_compact_difference_bound hG₀ (0 + 1)
  have Upos : 0 < C * D + E + 1 := by positivity
  apply sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _)))
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (C * D + E + 1)
  have hδ : 0 < δ := div_pos hε Upos
  obtain ⟨w, W, hw, hW, hPos, hwW, hCentral, hMass, hMoment⟩ := complexCentralPolynomialWeight n δ hδ
  obtain ⟨p, hp, hBproj⟩ := exists_polynomial_projection r ds a B hB w hw f g
  have hpK : compactProfile (finiteToSmooth p) = convolution w φ := by
    funext x
    change p.val (Unitary.toUnits x) = ∫ k : K n, w k * F.val (Unitary.toUnits (x * k)) ∂compactMatrixHaar n
    rw [hp (Unitary.toUnits x)]
    apply integral_congr_ae (ae_of_all _ fun k => ?_)
    change w k * f.val (Unitary.toUnits x * Unitary.toUnits k * g) =
      w k * f.val (Unitary.toUnits (x * k) * g)
    rw [Unitary.toUnits.map_mul]
  have hL : ‖L (finiteToSmooth p) - L F‖ ≤ C * (D * δ) := by
    rw [← map_sub]
    apply hBound
    rw [map_sub, hpK]
    exact convolution_error w W hW hPos hwW hCentral hMass hφ hD hDφ hMoment.le
  have hSample : ‖B p 1 - B f g‖ ≤ E * δ := by
    have hh := convolution_error w W hW hPos hwW hCentral hMass hψ hE hEψ hMoment.le [] le_rfl 1
    change ‖convolution w ψ 1 - ψ 1‖ ≤ E * δ * 1 at hh
    have hs : convolution w ψ 1 = B p 1 := by
      rw [hBproj]
      change (∫ k : K n, w k * B f (Unitary.toUnits (1 * k) * g) ∂compactMatrixHaar n) = _
      simp only [one_mul]
      rfl
    have ht : ψ 1 = B f g := by simp [ψ, G₀]
    simpa only [hs, ht, mul_one] using hh
  have hsum : (C * D + E) * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_le_iff₀ Upos, mul_comm (C * D + E) ε]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hε.le
  rw [hRestr p] at hL
  change ‖L F - B f g‖ ≤ 0 + ε
  rw [zero_add]
  calc
    _ = ‖(L F - B p 1) + (B p 1 - B f g)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖L F - B p 1‖ + ‖B p 1 - B f g‖ := norm_add_le _ _
    _ ≤ C * (D * δ) + E * δ := add_le_add (by rw [norm_sub_rev]; exact hL) hSample
    _ = (C * D + E) * δ := by ring
    _ ≤ ε := hsum

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslateExtension
