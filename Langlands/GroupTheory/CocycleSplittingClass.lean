import Langlands.GroupTheory.CocycleSplittingExtension
import Langlands.Cohomology.Tate.ScalarCupBoundary
import Langlands.Cohomology.Tate.OrdinaryTateBoundary

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

omit [Fintype G] in
lemma regular_delta (g h : G) :
    (regular G).ρ g (delta G h) = delta G (h * g⁻¹) := by
  classical
  funext x
  simp [regular_apply, delta, Pi.single_apply, eq_mul_inv_iff_mul_eq]

/-- The standard augmentation-ideal one-cocycle. -/
def augmentationCocycle (g : G) : Ideal G :=
  ⟨delta G g⁻¹ - delta G 1, by
    change coordinateSum G (delta G g⁻¹ - delta G 1) = 0
    rw [map_sub, coordinateSum_delta, coordinateSum_delta, sub_self]⟩

@[simp] lemma augmentationCocycle_val (g : G) :
    (augmentationCocycle g).val = delta G g⁻¹ - delta G 1 := rfl

lemma augmentationCocycle_action (g h : G) :
    (ideal G).ρ g (augmentationCocycle h) =
      augmentationCocycle (g * h) - augmentationCocycle g := by
  apply Subtype.ext
  change (regular G).ρ g (delta G h⁻¹ - delta G 1) =
    (delta G (g * h)⁻¹ - delta G 1) - (delta G g⁻¹ - delta G 1)
  rw [map_sub, regular_delta, regular_delta, one_mul, mul_inv_rev]
  abel

lemma augmentationCocycle_d₀₁ :
    (idealInclusion G).hom ∘ augmentationCocycle =
      groupCohomology.d₀₁ (regular G) (delta G 1) := by
  funext g
  change delta G g⁻¹ - delta G 1 =
    (show G → Scalars.{u} from (regular G).ρ g (delta G 1)) - delta G 1
  rw [regular_delta, one_mul]

/-- The augmentation-ideal cocycle in Mathlib's actual cocycle module. -/
def augmentationOneCocycle : groupCohomology.cocycles₁ (ideal G) :=
  ⟨augmentationCocycle, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁
    (idealSequence_shortExact G) augmentationCocycle_d₀₁⟩

variable (c : NormalizedTwoCocycle G A)

lemma twist_delta (g h : G) :
    twist c g (delta G h) = Additive.ofMul (c (g, h⁻¹)) := by
  classical
  simp [twist_apply, delta, Pi.single_apply]

lemma twist_augmentationCocycle (g h : G) :
    twist c g (augmentationCocycle h).val = Additive.ofMul (c (g, h)) := by
  rw [augmentationCocycle_val, map_sub, twist_delta, twist_delta]
  simp

lemma idealSequence_delta_unit :
    groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl
        ((groupCohomology.H0Iso (Tate.integralTrivial G)).inv ⟨1, fun _ => rfl⟩) =
      groupCohomology.H1π (ideal G) augmentationOneCocycle := by
  exact groupCohomology.δ₀_apply (idealSequence_shortExact G)
    ⟨(1 : Scalars.{u}), fun _ => rfl⟩ (delta G 1) (coordinateSum_delta G 1)
    augmentationCocycle augmentationCocycle_d₀₁

lemma splitting_d₁₂ :
    (inclusion c).hom ∘ (Additive.ofMul ∘ c) =
      groupCohomology.d₁₂ (splitting c)
        (fun g => (0, augmentationCocycle g)) := by
  funext ⟨g, h⟩
  apply Prod.ext
  · change Additive.ofMul (c (g, h)) =
      coefficientAction g 0 + twist c g (augmentationCocycle h).val - 0 + 0
    rw [map_zero, twist_augmentationCocycle]
    abel
  · change (0 : Ideal G) =
      (show Ideal G from (ideal G).ρ g (augmentationCocycle h)) -
        augmentationCocycle (g * h) + augmentationCocycle g
    rw [augmentationCocycle_action]
    change (0 : Ideal G) =
      (augmentationCocycle (g * h) - augmentationCocycle g) -
        augmentationCocycle (g * h) + augmentationCocycle g
    abel

lemma sequence_delta_augmentation :
    groupCohomology.δ (sequence_shortExact c) 1 2 rfl
        (groupCohomology.H1π (ideal G) augmentationOneCocycle) =
      cohomologyClass c := by
  exact groupCohomology.δ₁_apply (sequence_shortExact c)
    augmentationOneCocycle (fun g => (0, augmentationCocycle g)) rfl
    (Additive.ofMul ∘ c) (splitting_d₁₂ c)

/-- The ordinary double connecting map represents the given cocycle. -/
lemma ordinary_doubleBoundary :
    groupCohomology.δ (sequence_shortExact c) 1 2 rfl
        (groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl
          ((groupCohomology.H0Iso (Tate.integralTrivial G)).inv ⟨1, fun _ => rfl⟩)) =
      cohomologyClass c := by
  rw [idealSequence_delta_unit, sequence_delta_augmentation]

/-- The scalar double-boundary class of the actual splitting sequence is the
ordinary class of its normalized two-cocycle. -/
lemma scalarDoubleBoundaryClass_eq :
    Tate.scalarDoubleBoundaryClass (sequence c) (sequence_shortExact c)
        (idealInclusion G) (augmentation G) (idealSequence G).zero
        (idealSequence_shortExact G) =
      cohomologyClass c := by
  let unit : groupCohomology (Tate.integralTrivial G) 0 :=
    (groupCohomology.H0Iso (Tate.integralTrivial G)).inv ⟨1, fun _ => rfl⟩
  have h₀ := ConcreteCategory.congr_hom
    (Tate.ordinaryToTate_delta (idealSequence_shortExact G) 0) unit
  have h₁ := ConcreteCategory.congr_hom
    (Tate.ordinaryToTate_delta (sequence_shortExact c) 1)
    (groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl unit)
  change Tate.ordinaryToTate (ideal G) 1
      (groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl unit) =
    TateCohomology.δ (idealSequence_shortExact G) 0
      (Tate.ordinaryToTate (Tate.integralTrivial G) 0 unit) at h₀
  have hu : Tate.ordinaryToTate (Tate.integralTrivial G) 0 unit =
      Tate.scalarUnitClass (R := Scalars.{u}) (G := G) :=
    Tate.ordinaryToTate_zero_invariant _ _
  rw [hu] at h₀
  change Tate.ordinaryToTate (coefficientRepresentation G A) 2
      (groupCohomology.δ (sequence_shortExact c) 1 2 rfl
        (groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl unit)) =
    TateCohomology.δ (sequence_shortExact c) 1
      (Tate.ordinaryToTate (ideal G) 1
        (groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl unit)) at h₁
  rw [h₀] at h₁
  change Tate.ordinaryToTate (coefficientRepresentation G A) 2
      (groupCohomology.δ (sequence_shortExact c) 1 2 rfl
        (groupCohomology.δ (idealSequence_shortExact G) 0 1 rfl
          ((groupCohomology.H0Iso (Tate.integralTrivial G)).inv ⟨1, fun _ => rfl⟩))) =
    _ at h₁
  rw [ordinary_doubleBoundary] at h₁
  apply ((TateCohomology.isoGroupCohomology 2).app
    (coefficientRepresentation G A)).symm.toLinearEquiv.injective
  change ((TateCohomology.isoGroupCohomology 2).app
      (coefficientRepresentation G A)).inv
      (((TateCohomology.isoGroupCohomology 2).app
        (coefficientRepresentation G A)).hom _) = _
  rw [Iso.hom_inv_id_apply]
  exact h₁.symm

/-- Cup bijectivity for the given cocycle makes its actual splitting module
Tate acyclic in every integer degree. -/
lemma splitting_tate_isZero
    (hcup : ∀ n : ℤ, Function.Bijective
      (Tate.integralH2Cup (coefficientRepresentation G A) n (cohomologyClass c)))
    (n : ℤ) : IsZero (tateCohomology (splitting c) n) := by
  refine Tate.scalarDoubleBoundary_middle_isZero (sequence c) (sequence_shortExact c)
    (idealInclusion G) (augmentation G) (idealSequence G).zero
    (idealSequence_shortExact G) (sequence_scalarSplitting c)
    (idealSequence_scalarSplitting (G := G)) (regular_tate_isZero G) ?_ n
  intro m
  rw [scalarDoubleBoundaryClass_eq]
  exact hcup m

end Langlands.NormalizedTwoCocycle.SplittingModule
