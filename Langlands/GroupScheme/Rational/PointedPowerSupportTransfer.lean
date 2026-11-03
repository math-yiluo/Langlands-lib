import Langlands.GroupScheme.Rational.PointedFinitePowerSupport
import Langlands.GroupScheme.Rational.DominantPullbackProof

/-! # Augmentation support transferred by actual ordered product maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PointedCoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V : Over (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Ordered multiplication sends the tuple of distinguished points to the
identity whenever the original morphism does. -/
theorem orderedPowerMap_origin (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f) (n : ℕ) :
    (a.finitePower n).origin ≫ orderedPowerMap f n = η[G.X] := by
  change (a.finitePower n).origin ≫ orderedPowerMap f n = (PointedAction.ofGroup b).origin
  rw [orderedPowerMap_points]
  simp only [PointedAction.finitePower_origin_π, hf.2]
  have he : (PointedAction.ofGroup b).origin =
      (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) := by
    simp [PointedAction.ofGroup, Hom.one_def]
  simp [he, List.ofFn_const]

/-- The actual ordered product map is pointed equivariant for the existing
finite-power action. -/
theorem orderedPowerMap_isPointedEquivariant (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f) (n : ℕ) :
    IsPointedEquivariant (a.finitePower n) (PointedAction.ofGroup b)
      (orderedPowerMap f n) :=
  ⟨orderedPowerMap_equivariant a.toPointwiseSchemeAction b f hf.1 n,
    orderedPowerMap_origin a b f hf n⟩

variable [IsAffineHom V.hom] [IsAffineHom G.X.hom]

/-- The actual augmentation pullback along ordered multiplication of the
images of a finite tuple. -/
def orderedPowerAugmentationPullback (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f) (n : ℕ) :
    augmentation (PointedAction.ofGroup b) →ₗ[k] augmentation (a.finitePower n) :=
  augmentationPullback (a.finitePower n) (PointedAction.ofGroup b)
    (orderedPowerMap f n) (orderedPowerMap_isPointedEquivariant a b f hf n)

@[simp] theorem orderedPowerAugmentationPullback_coe (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f) (n : ℕ)
    (z : augmentation (PointedAction.ofGroup b)) :
    (orderedPowerAugmentationPullback a b f hf n z :
      Coord (GroupScheme.finitePower V n)) = pullback (orderedPowerMap f n) z := rfl

theorem orderedPowerAugmentationPullback_mem (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f) (n : ℕ)
    (χ : characterLattice S) {z : augmentation (PointedAction.ofGroup b)}
    (hz : z ∈ augmentationWeightSpace (PointedAction.ofGroup b) χ) :
    orderedPowerAugmentationPullback a b f hf n z ∈
      augmentationWeightSpace (a.finitePower n) χ :=
  augmentationPullback_mem (a.finitePower n) (PointedAction.ofGroup b)
    (orderedPowerMap f n) (orderedPowerMap_isPointedEquivariant a b f hf n) χ hz

theorem orderedPowerAugmentationPullback_injective (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f) (n : ℕ)
    (hinj : Function.Injective (pullback (orderedPowerMap f n))) :
    Function.Injective (orderedPowerAugmentationPullback a b f hf n) := by
  intro x y hxy
  apply Subtype.ext
  exact hinj (congrArg Subtype.val hxy)

/-- An injective actual ordered-product pullback transfers a semigroup support
bound from the source to the target group. -/
theorem orderedPower_support_subset_semigroup_of_injective
    (hS : IsSplitTorus S.toGrp) (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f)
    (P : AddSubsemigroup (characterLattice S)) (hP : support a ⊆ P) (n : ℕ)
    (hinj : Function.Injective (pullback (orderedPowerMap f n))) :
    CoordinateWeights.support b ⊆ P := by
  change support (PointedAction.ofGroup b) ⊆ P
  exact (support_subset_of_injective (a.finitePower n) (PointedAction.ofGroup b)
    (orderedPowerMap f n) (orderedPowerMap_isPointedEquivariant a b f hf n) hinj).trans
    (finitePower_support_subset_semigroup_of_split hS a P hP n)

/-- Dominance into a reduced affine group supplies the injectivity needed to
transfer the source augmentation-support bound. -/
theorem orderedPower_support_subset_semigroup_of_dominant
    (hS : IsSplitTorus S.toGrp) (a : PointedAction S V)
    (b : AutomorphicAction S.toGrp G) (f : V ⟶ G.X)
    (hf : IsPointedEquivariant a (PointedAction.ofGroup b) f)
    (P : AddSubsemigroup (characterLattice S)) (hP : support a ⊆ P) (n : ℕ)
    (hReduced : IsReduced G.X.left) (hDom : IsDominant (orderedPowerMap f n).left) :
    CoordinateWeights.support b ⊆ P :=
  orderedPower_support_subset_semigroup_of_injective hS a b f hf P hP n
    (dominantPullbackStatement k (GroupScheme.finitePower V n) G.X
      (orderedPowerMap f n) hReduced hDom)

end Langlands.GroupScheme.PointedCoordinateWeights
