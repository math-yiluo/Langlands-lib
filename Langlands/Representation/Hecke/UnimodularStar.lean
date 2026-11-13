import Langlands.Representation.Hecke.AntiPullback
import Langlands.Representation.Hecke.Corner

/-! # The unimodular involution on actual Hecke functions and corners -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ComplexConjugate

namespace Langlands.Hecke

universe uG

open HarmonicAnalysis (SchwartzBruhat)

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace TestFunction

/-- Conjugation followed by inversion on the actual test functions. -/
def adjoint : SchwartzBruhat G ≃ₗ⋆[ℂ] SchwartzBruhat G where
  toFun f :=
    ⟨fun x => conj (f x⁻¹),
      (f.locallyConstant.comp_continuous continuous_inv).comp conj,
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).comp_left (map_zero _)⟩
  invFun f :=
    ⟨fun x => conj (f x⁻¹),
      (f.locallyConstant.comp_continuous continuous_inv).comp conj,
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).comp_left (map_zero _)⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; exact map_add _ _ _
  map_smul' c f := by ext x; exact map_mul _ _ _

@[simp] theorem adjoint_apply (f : SchwartzBruhat G) (x : G) :
    adjoint f x = conj (f x⁻¹) := rfl

@[simp] theorem adjoint_adjoint (f : SchwartzBruhat G) :
    adjoint (adjoint f) = f := adjoint.left_inv f

/-- The involution interchanges left and right subgroup invariance. -/
theorem adjoint_mem_biInvariant {K L : Subgroup G} {f : SchwartzBruhat G}
    (hf : f ∈ biInvariant K L) : adjoint f ∈ biInvariant L K := by
  constructor
  · intro l x
    change conj (f (((l : G) * x)⁻¹)) = conj (f x⁻¹)
    rw [mul_inv_rev]
    exact congrArg conj (hf.2 l⁻¹ x⁻¹)
  · intro k x
    change conj (f ((x * (k : G))⁻¹)) = conj (f x⁻¹)
    rw [mul_inv_rev]
    exact congrArg conj (hf.1 k⁻¹ x⁻¹)

variable [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [IsMulRightInvariant μ] [IsInvInvariant μ]

/-- For an inversion-invariant right Haar measure, the adjoint reverses convolution. -/
theorem adjoint_convolution (f g : SchwartzBruhat G) :
    adjoint (convolution μ f g) = convolution μ (adjoint g) (adjoint f) := by
  have hinv := pullback_convolution μ (Homeomorph.inv G)
    (fun x y => mul_inv_rev x y) (measurePreserving_inv μ) f g
  ext x
  have hx := congrArg (fun h : SchwartzBruhat G => h x) hinv
  change (∫ y, f y * g (y⁻¹ * x⁻¹) ∂μ) =
    ∫ y, g y⁻¹ * f (y⁻¹ * x)⁻¹ ∂μ at hx
  change conj (∫ y, f y * g (y⁻¹ * x⁻¹) ∂μ) =
    ∫ y, conj (g y⁻¹) * conj (f (y⁻¹ * x)⁻¹) ∂μ
  rw [hx, ← integral_conj]
  congr 1
  funext y
  exact map_mul _ _ _

end TestFunction

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

namespace HeckeAlgebra

instance : Star (HeckeAlgebra μ) := ⟨TestFunction.adjoint⟩

@[simp] theorem star_apply (f : HeckeAlgebra μ) (x : G) :
    star f x = conj (f x⁻¹) := rfl

instance : InvolutiveStar (HeckeAlgebra μ) where
  star_involutive := TestFunction.adjoint_adjoint

instance : StarModule ℂ (HeckeAlgebra μ) where
  star_smul c f := TestFunction.adjoint.map_smulₛₗ c f

variable [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
  [IsMulRightInvariant μ] [IsInvInvariant μ]

instance : StarRing (HeckeAlgebra μ) where
  star_involutive := TestFunction.adjoint_adjoint
  star_mul := TestFunction.adjoint_convolution μ
  star_add := TestFunction.adjoint.map_add

end HeckeAlgebra

variable [μ.IsHaarMeasure]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

namespace HeckeAlgebra

@[simp] theorem star_normalizedIndicator :
    star (normalizedIndicator μ K hK) = normalizedIndicator μ K hK := by
  ext x
  simp only [star_apply, normalizedIndicator_apply, map_mul, map_inv₀,
    Complex.conj_ofReal]
  by_cases hx : x ∈ K
  · simp [hx, K.inv_mem hx]
  · have hx' : x⁻¹ ∉ K := fun h => hx (K.inv_mem_iff.mp h)
    simp [hx, hx']

namespace Corner

instance : Star (Corner μ K hK) :=
  ⟨fun f => ⟨star (toHeckeAlgebra μ K hK f),
    TestFunction.adjoint_mem_biInvariant f.property⟩⟩

@[simp] theorem toHeckeAlgebra_star (f : Corner μ K hK) :
    toHeckeAlgebra μ K hK (star f) = star (toHeckeAlgebra μ K hK f) := rfl

@[simp] theorem star_apply (f : Corner μ K hK) (x : G) :
    star f x = conj (f x⁻¹) := rfl

instance : InvolutiveStar (Corner μ K hK) where
  star_involutive f := Subtype.ext (star_star (toHeckeAlgebra μ K hK f))

instance : StarModule ℂ (Corner μ K hK) where
  star_smul c f := Subtype.ext (star_smul c (toHeckeAlgebra μ K hK f))

variable [IsMulRightInvariant μ] [IsInvInvariant μ]

instance : StarRing (Corner μ K hK) where
  star_involutive f := Subtype.ext (star_star (toHeckeAlgebra μ K hK f))
  star_mul f g := Subtype.ext (star_mul (toHeckeAlgebra μ K hK f)
    (toHeckeAlgebra μ K hK g))
  star_add f g := Subtype.ext (star_add (toHeckeAlgebra μ K hK f)
    (toHeckeAlgebra μ K hK g))

end Corner
end HeckeAlgebra
end Langlands.Hecke
