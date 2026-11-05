import Langlands.AlgebraicGeometry.Deformation.ArtinianQuotients
import Langlands.AlgebraicGeometry.Picard.StackAtlas

/-! # Elementary lifting for actual Picard chart points on Artinian tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation

namespace ArtinianChartLifting

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {U : Over (Spec (CommRingCat.of k))}
  (L : LineBundle ((relativeSpace f).obj U))

private abbrev FiberPoints {T : Over (Spec (CommRingCat.of k))}
    (M : LineBundle ((relativeSpace f).obj T)) (Z : Over T) :=
  Langlands.CategoryTheory.PseudofunctorPointFiber.Points
    (relative f) (Core.mk L) (Core.mk M) Z

/-- The actual slice arrow induced by a compatible Artinian algebra map. -/
def testArrow {A B : ArtinianTest k K} (q : A ⟶ B)
    {T : Over (Spec (CommRingCat.of k))}
    {a : ArtinianTest.base A ⟶ T} {b : ArtinianTest.base B ⟶ T}
    (w : ArtinianTest.baseMap q ≫ a = b) :
    Over.mk b ⟶ Over.mk a :=
  Over.homMk (ArtinianTest.baseMap q) w

/-- Restriction retains both the actual chart map and the specified bundle isomorphism. -/
def restrict {A B : ArtinianTest k K} (q : A ⟶ B)
    {T : Over (Spec (CommRingCat.of k))}
    (M : LineBundle ((relativeSpace f).obj T))
    {a : ArtinianTest.base A ⟶ T} {b : ArtinianTest.base B ⟶ T}
    (w : ArtinianTest.baseMap q ≫ a = b) :
    FiberPoints f L M (Over.mk a) → FiberPoints f L M (Over.mk b) :=
  Langlands.CategoryTheory.PseudofunctorPointFiber.restrict
    (relative f) (Core.mk L) (Core.mk M) (testArrow q w)

/-- The restricted point has the composite actual map into the chart scheme. -/
lemma restrict_baseMap {A B : ArtinianTest k K} (q : A ⟶ B)
    {T : Over (Spec (CommRingCat.of k))}
    (M : LineBundle ((relativeSpace f).obj T))
    {a : ArtinianTest.base A ⟶ T} {b : ArtinianTest.base B ⟶ T}
    (w : ArtinianTest.baseMap q ≫ a = b) (x : FiberPoints f L M (Over.mk a)) :
    (restrict f L q M w x).1 = ArtinianTest.baseMap q ≫ x.1 := rfl

/-- A family lifts actual chart points, including their specified isomorphisms,
along this algebra arrow on every compatible slice test. -/
def HasLiftingFor {A B : ArtinianTest k K} (q : A ⟶ B) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k)))
    (M : LineBundle ((relativeSpace f).obj T))
    (a : ArtinianTest.base A ⟶ T) (b : ArtinianTest.base B ⟶ T)
    (w : ArtinianTest.baseMap q ≫ a = b),
      Function.Surjective (restrict f L q M w)

/-- Lifting actual points is stable under composition of test arrows. -/
lemma hasLiftingFor_comp {A B C : ArtinianTest k K} (q : A ⟶ B) (r : B ⟶ C)
    (hq : HasLiftingFor f L q) (hr : HasLiftingFor f L r) :
    HasLiftingFor f L (q ≫ r) := by
  intro T M a c w x
  let b : ArtinianTest.base B ⟶ T := ArtinianTest.baseMap q ≫ a
  have wr : ArtinianTest.baseMap r ≫ b = c := by
    dsimp only [b]
    rw [← Category.assoc, ArtinianTest.baseMap_comp, w]
  obtain ⟨y, hy⟩ := hr T M b c wr x
  obtain ⟨z, hz⟩ := hq T M a b rfl y
  refine ⟨z, ?_⟩
  have hm : testArrow (q ≫ r) w = testArrow r wr ≫ testArrow q rfl := by
    apply Over.OverMorphism.ext
    exact (ArtinianTest.baseMap_comp q r).symm
  change Langlands.CategoryTheory.PseudofunctorPointFiber.restrict
    (relative f) (Core.mk L) (Core.mk M) (testArrow (q ≫ r) w) z = x
  rw [hm, Langlands.CategoryTheory.PseudofunctorPointFiber.restrict_comp]
  change restrict f L r M wr (restrict f L q M rfl z) = x
  rw [hz, hy]

/-- Formal lifting on augmented Artinian tests with the specified residue field. -/
def IsFormallySmoothOnTests (K : Type u) [Field K] [Algebra k K] : Prop :=
  ∀ {A B : ArtinianTest k K} (q : A ⟶ B),
    Function.Surjective (ArtinianTest.toAlgHom q) → HasLiftingFor f L q

/-- Formal lifting can be checked on maximal-ideal-annihilated kernels,
without discarding any prescribed bundle isomorphism. -/
theorem isFormallySmoothOnTests_iff_elementary :
    IsFormallySmoothOnTests f L K ↔
      ∀ {A B : ArtinianTest k K} (q : A ⟶ B),
        ArtinianTest.IsElementarySurjection q → HasLiftingFor f L q := by
  constructor
  · intro h A B q hq
    exact h q hq.1
  · intro h A B q hq
    exact ArtinianTest.surjective_induction
      (fun {_ _} q ↦ HasLiftingFor f L q) h
      (fun q r hq hr ↦ hasLiftingFor_comp f L q r hq hr) q hq

end ArtinianChartLifting

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
