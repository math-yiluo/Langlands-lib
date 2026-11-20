import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.Representation.Hecke.DoubleCosetSandwich

/-! # Character twists of compact-open Hecke corners -/

noncomputable section

namespace Langlands.Hecke.HeckeAlgebra.Corner

open MeasureTheory
open Langlands.HarmonicAnalysis.Distribution (multiplyTest)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (μ : Measure G) [μ.IsHaarMeasure]
variable (χ : G →* ℂˣ) (hχ : ∀ k : K, χ (k : G) = 1)

private def locallyConstantCharacter : LocallyConstant G ℂ := by
  refine ⟨fun x => (χ x : ℂ), (IsLocallyConstant.iff_exists_open _).2 ?_⟩
  intro x
  refine ⟨(fun k => x * k) '' (K : Set G), isOpenMap_mul_left x _ K.isOpen,
    ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  change (χ (x * k) : ℂ) = (χ x : ℂ)
  rw [map_mul, hχ ⟨k, hk⟩, mul_one]

private def characterTwistLinear : Corner μ K hK →ₗ[ℂ] Corner μ K hK where
  toFun f := by
    let f' := multiplyTest (locallyConstantCharacter K χ hχ)
      (toTestFunction μ (toHeckeAlgebra μ K hK f))
    refine ⟨f', ?_⟩
    change f' ∈ TestFunction.biInvariant K.toSubgroup K.toSubgroup
    constructor
    · intro k x
      change (χ ((k : G) * x) : ℂ) * f ((k : G) * x) = (χ x : ℂ) * f x
      rw [map_mul, hχ k, one_mul, leftInvariant]
    · intro k x
      change (χ (x * (k : G)) : ℂ) * f (x * (k : G)) = (χ x : ℂ) * f x
      rw [map_mul, hχ k, mul_one, rightInvariant]
  map_add' f g := by
    apply ext' K hK μ
    intro x
    change (χ x : ℂ) * (f x + g x) = (χ x : ℂ) * f x + (χ x : ℂ) * g x
    exact mul_add _ _ _
  map_smul' c f := by
    apply ext' K hK μ
    intro x
    change (χ x : ℂ) * (c * f x) = c * ((χ x : ℂ) * f x)
    exact mul_left_comm _ _ _

/-- Pointwise multiplication by a character trivial on the level preserves the
unit, convolution, and scalars of the compact-open Hecke corner. -/
def characterTwist : Corner μ K hK →ₐ[ℂ] Corner μ K hK :=
  AlgHom.ofLinearMap (characterTwistLinear K hK μ χ hχ) (by
    apply ext' K hK μ
    intro x
    change (χ x : ℂ) * (1 : Corner μ K hK) x = (1 : Corner μ K hK) x
    rw [one_apply]
    by_cases hx : x ∈ (K : Set G)
    · have he : χ x = 1 := hχ ⟨x, hx⟩
      rw [he, Units.val_one, one_mul]
    · rw [Set.indicator_of_notMem hx, mul_zero, mul_zero]) (by
    intro f g
    apply ext' K hK μ
    intro x
    change (χ x : ℂ) * (f * g) x =
      (characterTwistLinear K hK μ χ hχ f * characterTwistLinear K hK μ χ hχ g) x
    rw [mul_apply, mul_apply, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    change (χ x : ℂ) * (f y * g (y⁻¹ * x)) =
      ((χ y : ℂ) * f y) * ((χ (y⁻¹ * x) : ℂ) * g (y⁻¹ * x))
    have he : χ y * χ (y⁻¹ * x) = χ x := by rw [← map_mul, mul_inv_cancel_left]
    rw [← he, Units.val_mul]
    ring)

@[simp]
theorem characterTwist_apply (f : Corner μ K hK) (x : G) :
    characterTwist K hK μ χ hχ f x = (χ x : ℂ) * f x := rfl

variable [T2Space G]

theorem characterTwist_doubleCoset (g : G) :
    characterTwist K hK μ χ hχ (doubleCoset K hK μ g) =
      (χ g : ℂ) • doubleCoset K hK μ g := by
  apply ext' K hK μ
  intro x
  rw [characterTwist_apply, smul_apply]
  by_cases hx : x ∈ TestFunction.doubleCosetSet K g
  · obtain ⟨a, ha, b, hb, rfl⟩ := (TestFunction.mem_doubleCosetSet K g x).1 hx
    have ha' : χ a = 1 := hχ ⟨a, ha⟩
    have hb' : χ b = 1 := hχ ⟨b, hb⟩
    rw [map_mul, map_mul, ha', hb', one_mul, mul_one]
  · rw [doubleCoset_apply, Set.indicator_of_notMem hx, mul_zero, mul_zero, mul_zero]

end Langlands.Hecke.HeckeAlgebra.Corner
