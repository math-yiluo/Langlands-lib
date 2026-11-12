import Langlands.GroupTheory.CocycleSplittingClass
import Langlands.Cohomology.Tate.MinusTwoBoundary

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

variable {G A : Type u} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A]

local instance : Module Scalars.{u} (Additive A) := ULift.module
local instance : Module Scalars.{u} (Rep.ofMulDistribMulAction G A) := ULift.module

lemma augmentationCocycle_norm (g : G) :
    (ideal G).ρ.norm (augmentationCocycle g) = 0 := by
  apply (Rep.mono_iff_injective (idealInclusion G)).mp (idealSequence_shortExact G).mono_f
  rw [map_zero]
  have hn := congrArg (fun f : ideal G ⟶ regular G => f.hom (augmentationCocycle g))
    (Rep.norm_comm (idealInclusion G))
  change (regular G).ρ.norm (delta G g⁻¹ - delta G 1) =
    (idealInclusion G).hom ((ideal G).ρ.norm (augmentationCocycle g)) at hn
  rw [← hn]
  rw [← one_mul g⁻¹, ← regular_delta, map_sub, Representation.norm_self_apply, sub_self]

variable (c : NormalizedTwoCocycle G A)

/-- Sum of cocycle entries selected by the inverse of the single-chain index. -/
def inverseRowSum (g : G) : Additive A :=
  ∑ h : G, Additive.ofMul (c (h, g⁻¹))

lemma splitting_norm_augmentation (g : G) :
    (splitting c).ρ.norm (0, augmentationCocycle g⁻¹) =
      (inverseRowSum c g, 0) := by
  simp only [splitting, Representation.norm, LinearMap.sum_apply]
  apply Prod.ext
  · simp only [Prod.fst_sum]
    change (∑ h : G, (coefficientAction h 0 +
        twist c h (augmentationCocycle g⁻¹).val)) = inverseRowSum c g
    simp only [map_zero, zero_add, twist_augmentationCocycle, inverseRowSum]
  · simp only [Prod.snd_sum]
    change (∑ h : G, (ideal G).ρ h (augmentationCocycle g⁻¹)) = 0
    simpa only [Representation.norm, LinearMap.sum_apply] using augmentationCocycle_norm g⁻¹

/-- The displayed cocycle sum is invariant because it is the coefficient
component of a norm in the splitting representation. -/
def inverseRowInvariant (g : G) : (coefficientRepresentation G A).ρ.invariants :=
  ⟨(show Additive A from inverseRowSum c g), fun h => by
    have hn := (splitting c).ρ.self_norm_apply h (0, augmentationCocycle g⁻¹)
    rw [splitting_norm_augmentation] at hn
    have hf := congrArg Prod.fst hn
    change coefficientAction h (inverseRowSum c g) + twist c h 0 = inverseRowSum c g at hf
    change coefficientAction h (inverseRowSum c g) = inverseRowSum c g
    exact (by simpa only [map_zero, add_zero] using hf)⟩

/-- Explicit degree-minus-two scalar cup evaluation for any normalized cocycle. -/
lemma scalarH2Cup_minusTwoClass (g : G) :
    Tate.scalarH2Cup (coefficientRepresentation G A) (-2) (cohomologyClass c)
        (Tate.minusTwoClass (Tate.integralTrivial G) g 1) =
      Tate.zeroClass (coefficientRepresentation G A) (inverseRowInvariant c g) := by
  rw [← scalarDoubleBoundaryClass_eq c]
  change Tate.scalarH2Cup (sequence c).X₁ (-2)
    (Tate.scalarDoubleBoundaryClass (sequence c) (sequence_shortExact c)
      (idealInclusion G) (augmentation G) (idealSequence G).zero
      (idealSequence_shortExact G)) _ = _
  rw [Tate.scalarH2Cup_doubleBoundary (sequence c) (sequence_shortExact c)
    (idealInclusion G) (augmentation G) (idealSequence G).zero
    (idealSequence_shortExact G) (sequence_scalarSplitting c)
    (idealSequence_scalarSplitting (G := G))]
  have : (idealSequence G).X₃.IsTrivial := inferInstanceAs (Tate.integralTrivial G).IsTrivial
  have hfirst := Tate.delta_minusTwoClass (idealSequence_shortExact G) g (1 : Scalars.{u})
    (delta G 1) (coordinateSum_delta G 1) (augmentationCocycle g⁻¹)
    (augmentationCocycle_norm g⁻¹) (by
      change delta G (g⁻¹)⁻¹ - delta G 1 = (show G → Scalars.{u} from (regular G).ρ g⁻¹ (delta G 1)) - delta G 1
      rw [regular_delta, one_mul])
  change TateCohomology.δ (sequence_shortExact c) (-1)
    (TateCohomology.δ (idealSequence_shortExact G) (-2)
      (Tate.minusTwoClass (Tate.integralTrivial G) g 1)) = _
  change TateCohomology.δ (idealSequence_shortExact G) (-2)
    (Tate.minusTwoClass (Tate.integralTrivial G) g (1 : Scalars.{u})) =
    Tate.minusOneClass (ideal G) (augmentationCocycle g⁻¹) (augmentationCocycle_norm g⁻¹) at hfirst
  exact (congrArg (fun x => TateCohomology.δ (sequence_shortExact c) (-1) x) hfirst).trans (by
    exact Tate.delta_minusOneClass (sequence_shortExact c)
      (augmentationCocycle g⁻¹) (augmentationCocycle_norm g⁻¹)
      (0, augmentationCocycle g⁻¹) rfl (inverseRowInvariant c g)
      (splitting_norm_augmentation c g).symm)

end Langlands.NormalizedTwoCocycle.SplittingModule
