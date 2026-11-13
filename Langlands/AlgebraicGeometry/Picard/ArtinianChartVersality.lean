import Langlands.AlgebraicGeometry.Deformation.ArtinianAugmentationArrow
import Langlands.AlgebraicGeometry.Picard.ArtinianChartLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianTestDeformations
import Langlands.AlgebraicGeometry.Deformation.ArtinianDualNumbers

/-! # Actual Picard chart lifting at a specified residue-field map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation

namespace ArtinianChartVersality

open ArtinianChartLifting

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {U : Over (Spec (CommRingCat.of k))}
  (L : LineBundle ((relativeSpace f).obj U))
  (p : ArtinianTest.residueBase k K ⟶ U)

/-- The actual fibre points, including their specified bundle isomorphisms. -/
abbrev FiberPoints {T : Over (Spec (CommRingCat.of k))}
    (M : LineBundle ((relativeSpace f).obj T)) (Z : Over T) :=
  Langlands.CategoryTheory.PseudofunctorPointFiber.Points
    (relative f) (Core.mk L) (Core.mk M) Z

/-- The specified residue map of a lift is forced by its actual restriction. -/
lemma residueMap_of_restrict_eq {A B : ArtinianTest k K} (q : A ⟶ B)
    {T : Over (Spec (CommRingCat.of k))}
    (M : LineBundle ((relativeSpace f).obj T))
    {a : ArtinianTest.base A ⟶ T} {b : ArtinianTest.base B ⟶ T}
    (w : ArtinianTest.baseMap q ≫ a = b)
    {x : FiberPoints f L M (Over.mk a)} {y : FiberPoints f L M (Over.mk b)}
    (h : restrict f L q M w x = y) :
    ArtinianTest.reduction A ≫ x.1 = ArtinianTest.reduction B ≫ y.1 := by
  rw [← h, restrict_baseMap, ← Category.assoc, ArtinianTest.reduction_baseMap]

/-- Lifting at a specified residue map preserves the actual chart point and
the complete specified bundle isomorphism, on every compatible slice test. -/
def HasLiftingForAt {A B : ArtinianTest k K} (q : A ⟶ B) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k)))
    (M : LineBundle ((relativeSpace f).obj T))
    (a : ArtinianTest.base A ⟶ T) (b : ArtinianTest.base B ⟶ T)
    (w : ArtinianTest.baseMap q ≫ a = b)
    (y : FiberPoints f L M (Over.mk b)),
    ArtinianTest.reduction B ≫ y.1 = p →
      ∃ x : FiberPoints f L M (Over.mk a), restrict f L q M w x = y

/-- A lifted point has the same specified residue map, without a new choice. -/
lemma exists_lift_at {A B : ArtinianTest k K} {q : A ⟶ B}
    (h : HasLiftingForAt f L p q)
    (T : Over (Spec (CommRingCat.of k)))
    (M : LineBundle ((relativeSpace f).obj T))
    (a : ArtinianTest.base A ⟶ T) (b : ArtinianTest.base B ⟶ T)
    (w : ArtinianTest.baseMap q ≫ a = b)
    (y : FiberPoints f L M (Over.mk b))
    (hy : ArtinianTest.reduction B ≫ y.1 = p) :
    ∃ x : FiberPoints f L M (Over.mk a),
      ArtinianTest.reduction A ≫ x.1 = p ∧ restrict f L q M w x = y := by
  obtain ⟨x, hx⟩ := h T M a b w y hy
  exact ⟨x, (residueMap_of_restrict_eq f L q M w hx).trans hy, hx⟩

/-- Lifting at the same specified residue map is stable under composition. -/
lemma hasLiftingForAt_comp {A B C : ArtinianTest k K}
    (q : A ⟶ B) (r : B ⟶ C)
    (hq : HasLiftingForAt f L p q) (hr : HasLiftingForAt f L p r) :
    HasLiftingForAt f L p (q ≫ r) := by
  intro T M a c w x hx
  let b : ArtinianTest.base B ⟶ T := ArtinianTest.baseMap q ≫ a
  have wr : ArtinianTest.baseMap r ≫ b = c := by
    dsimp only [b]
    rw [← Category.assoc, ArtinianTest.baseMap_comp, w]
  obtain ⟨y, hy⟩ := hr T M b c wr x hx
  have hyp : ArtinianTest.reduction B ≫ y.1 = p :=
    (residueMap_of_restrict_eq f L r M wr hy).trans hx
  obtain ⟨z, hz⟩ := hq T M a b rfl y hyp
  refine ⟨z, ?_⟩
  have hm : testArrow (q ≫ r) w = testArrow r wr ≫ testArrow q rfl := by
    apply Over.OverMorphism.ext
    exact (ArtinianTest.baseMap_comp q r).symm
  change Langlands.CategoryTheory.PseudofunctorPointFiber.restrict
    (relative f) (Core.mk L) (Core.mk M) (testArrow (q ≫ r) w) z = x
  rw [hm, Langlands.CategoryTheory.PseudofunctorPointFiber.restrict_comp]
  change restrict f L r M wr (restrict f L q M rfl z) = x
  rw [hz, hy]

/-- Actual infinitesimal versality at the specified residue-field map:
every surjection of augmented Artinian tests lifts actual fibre points there. -/
def IsFormallyVersalAt : Prop :=
  ∀ {A B : ArtinianTest k K} (q : A ⟶ B),
    Function.Surjective (ArtinianTest.toAlgHom q) → HasLiftingForAt f L p q

/-- The actual pointed lifting condition can be checked on elementary kernels. -/
theorem isFormallyVersalAt_iff_elementary :
    IsFormallyVersalAt f L p ↔
      ∀ {A B : ArtinianTest k K} (q : A ⟶ B),
        ArtinianTest.IsElementarySurjection q → HasLiftingForAt f L p q := by
  constructor
  · intro h A B q hq
    exact h q hq.1
  · intro h A B q hq
    exact ArtinianTest.surjective_induction
      (fun {_ _} q ↦ HasLiftingForAt f L p q) h
      (fun q r hq hr ↦ hasLiftingForAt_comp f L p q r hq hr) q hq

/-- Lifting on a fixed test arrow is equivalent to lifting at all its
specified residue-field maps into the same actual family. -/
lemma hasLiftingFor_iff_forall_at {A B : ArtinianTest k K} (q : A ⟶ B) :
    HasLiftingFor f L q ↔
      ∀ p : ArtinianTest.residueBase k K ⟶ U, HasLiftingForAt f L p q := by
  constructor
  · intro h p T M a b w y _
    exact h T M a b w y
  · intro h T M a b w y
    exact h (ArtinianTest.reduction B ≫ y.1) T M a b w y rfl

/-- Formal lifting on all tests is the conjunction of the specified-residue
conditions, without restricting the scheme or the slice test. -/
theorem isFormallySmoothOnTests_iff_forall_versalAt :
    IsFormallySmoothOnTests f L K ↔
      ∀ p : ArtinianTest.residueBase k K ⟶ U, IsFormallyVersalAt f L p := by
  constructor
  · intro h p A B q hq
    exact (hasLiftingFor_iff_forall_at f L q).mp (h q hq) p
  · intro h A B q hq
    exact (hasLiftingFor_iff_forall_at f L q).mpr (fun p ↦ h p q hq)

/-- The residue pullback of the actual family at the specified point. -/
abbrev residueBundle :=
  (LineBundle.pullback ((relativeSpace f).map p)).obj L

/-- The spectrum map of the augmentation is the prescribed residue inclusion. -/
lemma augmentationArrow_baseMap (A : ArtinianTest k K) :
    ArtinianTest.baseMap (augmentationArrow A) = ArtinianTest.reduction A := rfl

/-- The residue test has the identity residue inclusion. -/
lemma reduction_residue :
    ArtinianTest.reduction (ArtinianTest.residue k K) =
      𝟙 (ArtinianTest.residueBase k K) := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

/-- A pointed deformation determines its exact residue fibre point, including
the originally specified reduction isomorphism. -/
def residuePoint (A : ArtinianTest k K)
    (N : ArtinianTestDeformations.Deformations f (residueBundle f L p) A) :
    FiberPoints f L N.right.of (Over.mk (ArtinianTest.reduction A)) :=
  ⟨p, asIso N.hom⟩

/-- The canonical residue fibre point has the specified map into the family. -/
lemma residuePoint_map (A : ArtinianTest k K)
    (N : ArtinianTestDeformations.Deformations f (residueBundle f L p) A) :
    (residuePoint f L p A N).1 = p := rfl

/-- Formal versality realizes every actual pointed Artinian deformation.
The equality of actual fibre points retains its full prescribed reduction. -/
theorem exists_realization_point (h : IsFormallyVersalAt f L p)
    (A : ArtinianTest k K)
    (N : ArtinianTestDeformations.Deformations f (residueBundle f L p) A) :
    ∃ x : FiberPoints f L N.right.of (Over.mk (𝟙 (ArtinianTest.base A))),
      ArtinianTest.reduction A ≫ x.1 = p ∧
        restrict f L (augmentationArrow A) N.right.of (Category.comp_id _)
          x = residuePoint f L p A N := by
  apply exists_lift_at f L p
    (h (augmentationArrow A) A.augmentation_surjective)
    (ArtinianTest.base A) N.right.of (𝟙 _) (ArtinianTest.reduction A)
    (Category.comp_id _) (residuePoint f L p A N)
  rw [residuePoint_map, reduction_residue, Category.id_comp]

/-- Remove identity pullback from a realization point, using the actual
relative pseudofunctor identity comparison. -/
def realizationIso (A : ArtinianTest k K)
    (N : ArtinianTestDeformations.Deformations f (residueBundle f L p) A)
    (x : FiberPoints f L N.right.of (Over.mk (𝟙 (ArtinianTest.base A)))) :
    (LineBundle.pullback ((relativeSpace f).map x.1)).obj L ≅ N.right.of :=
  (x.2 ≪≫
    (Cat.Hom.toNatIso ((relative f).mapId (.mk (op (ArtinianTest.base A))))).app
      N.right).hom.iso

end ArtinianChartVersality

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
