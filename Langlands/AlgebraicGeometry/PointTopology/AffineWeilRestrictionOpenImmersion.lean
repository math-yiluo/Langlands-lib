import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionOpenLocus
import Mathlib.CategoryTheory.Yoneda

/-! # Actual open immersions under affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable {X Y : Over (Spec (CommRingCat.of B))}
  [IsAffine X.left] [IsAffine Y.left]
  [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

/-- The existing coordinate morphism agrees with the universal comparison
after postcomposition, on every affine test. -/
theorem affineWeilRestrictionComparison_postcomp_affine
    (f : X ⟶ Y) (T : Type u) [CommRing T] [Algebra A T]
    (p : RingPoint A (affineWeilRestriction A B X) T) :
    affineWeilRestrictionComparison A B Y (ringTest A T)
        (p ≫ affineWeilRestrictionMap A B f) =
      affineWeilRestrictionComparison A B X (ringTest A T) p ≫ f := by
  rw [affineWeilRestrictionComparison_affine,
    affineWeilRestrictionPointEquiv_natural,
    affineWeilRestrictionComparison_affine, Category.assoc]

/-- The constructed affine maps commute with the actual universal counit. -/
theorem affineWeilRestrictionCounit_natural (f : X ⟶ Y) :
    (Over.pullback (Spec.algebraMap A B)).map (affineWeilRestrictionMap A B f) ≫
        affineWeilRestrictionCounit A B Y =
      affineWeilRestrictionCounit A B X ≫ f := by
  have h := affineWeilRestrictionComparison_postcomp_affine A B f
    (Langlands.Algebra.WeilRestrictionFiniteType A B (AffineCoordinateRing B X))
    (𝟙 (affineWeilRestriction A B X))
  dsimp only [affineWeilRestrictionComparison] at h
  erw [Category.id_comp,
    (Over.pullback (Spec.algebraMap A B)).map_id (affineWeilRestriction A B X),
    Category.id_comp] at h
  exact h

/-- Naturality in the original affine scheme, for arbitrary test schemes. -/
theorem affineWeilRestrictionComparison_postcomp (f : X ⟶ Y)
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineWeilRestriction A B X) :
    affineWeilRestrictionComparison A B Y T (p ≫ affineWeilRestrictionMap A B f) =
      affineWeilRestrictionComparison A B X T p ≫ f := by
  dsimp only [affineWeilRestrictionComparison]
  rw [Functor.map_comp, Category.assoc, affineWeilRestrictionCounit_natural,
    ← Category.assoc]

/-- An actual relative open immersion identifies its source with its open
range, over the original base. -/
def relativeOpenImmersionRangeIso (R : Type u) [CommRing R]
    {V W : Over (Spec (CommRingCat.of R))} (f : V ⟶ W)
    [IsOpenImmersion f.left] :
    V ≅ openOver R W f.left.opensRange := by
  let e := IsOpenImmersion.isoOfRangeEq f.left f.left.opensRange.ι
    (by rw [Scheme.Opens.range_ι]; rfl)
  exact Over.isoMk e (by
    change e.hom ≫ (f.left.opensRange.ι ≫ W.hom) = V.hom
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w])

@[simp]
theorem relativeOpenImmersionRangeIso_hom_fac (R : Type u) [CommRing R]
    {V W : Over (Spec (CommRingCat.of R))} (f : V ⟶ W)
    [IsOpenImmersion f.left] :
    (relativeOpenImmersionRangeIso R f).hom ≫ openOverι R W f.left.opensRange = f := by
  apply Over.OverMorphism.ext
  dsimp only [relativeOpenImmersionRangeIso, Over.isoMk, openOverι]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac f.left f.left.opensRange.ι
    (by rw [Scheme.Opens.range_ι]; rfl)

@[simp]
theorem relativeOpenImmersionRangeIso_inv_fac (R : Type u) [CommRing R]
    {V W : Over (Spec (CommRingCat.of R))} (f : V ⟶ W)
    [IsOpenImmersion f.left] :
    (relativeOpenImmersionRangeIso R f).inv ≫ f = openOverι R W f.left.opensRange := by
  calc
    _ = (relativeOpenImmersionRangeIso R f).inv ≫
        ((relativeOpenImmersionRangeIso R f).hom ≫ openOverι R W f.left.opensRange) :=
      congrArg (fun g => (relativeOpenImmersionRangeIso R f).inv ≫ g)
        (relativeOpenImmersionRangeIso_hom_fac R f).symm
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (f : X ⟶ Y) [IsOpenImmersion f.left]

/-- The existing affine map lands in the open locus of the original open
immersion's range. -/
theorem affineWeilRestrictionMap_range_subset_openLocus :
    Set.range (affineWeilRestrictionMap A B f).left ⊆
      affineWeilRestrictionOpenLocus A B Y f.left.opensRange := by
  apply (range_subset_affineWeilRestrictionOpenLocus_iff A B Y f.left.opensRange
    (affineWeilRestriction A B X) (affineWeilRestrictionMap A B f)).mpr
  dsimp only [affineWeilRestrictionComparison]
  rw [affineWeilRestrictionCounit_natural]
  rintro _ ⟨t, rfl⟩
  exact ⟨(affineWeilRestrictionCounit A B X).left t, rfl⟩

/-- The actual factor of the existing affine Weil-restriction map through the
open subscheme representing the original open range. -/
def affineWeilRestrictionOpenImmersionFactor :
    affineWeilRestriction A B X ⟶
      openAffineWeilRestriction A B Y f.left.opensRange :=
  relativeOpenLift A (affineWeilRestrictionMap A B f)
    (affineWeilRestrictionOpenLocus A B Y f.left.opensRange)
    (affineWeilRestrictionMap_range_subset_openLocus A B f)

@[simp]
theorem affineWeilRestrictionOpenImmersionFactor_fac :
    affineWeilRestrictionOpenImmersionFactor A B f ≫
        openOverι A (affineWeilRestriction A B Y)
          (affineWeilRestrictionOpenLocus A B Y f.left.opensRange) =
      affineWeilRestrictionMap A B f :=
  relativeOpenLift_fac _ _ _ _

/-- On every test scheme the factor corresponds to the original open
immersion's identification with its open range. -/
theorem affineWeilRestrictionOpenImmersionFactor_comparison
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineWeilRestriction A B X) :
    openAffineWeilRestrictionComparison A B Y f.left.opensRange T
        (p ≫ affineWeilRestrictionOpenImmersionFactor A B f) =
      affineWeilRestrictionComparison A B X T p ≫
        (relativeOpenImmersionRangeIso B f).hom := by
  let i := openOverι B Y f.left.opensRange
  let : Mono i.left := inferInstanceAs (Mono f.left.opensRange.ι)
  let : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  change _ ≫ openOverι B Y f.left.opensRange = _
  rw [openAffineWeilRestrictionComparison_fac, Category.assoc,
    affineWeilRestrictionOpenImmersionFactor_fac,
    affineWeilRestrictionComparison_postcomp, Category.assoc]
  exact congrArg (fun g => affineWeilRestrictionComparison A B X T p ≫ g)
    (relativeOpenImmersionRangeIso_hom_fac B f).symm

/-- The open-locus factor is an isomorphism, by its effect on all test
schemes and the already constructed representability comparisons. -/
instance affineWeilRestrictionOpenImmersionFactor_isIso :
    IsIso (affineWeilRestrictionOpenImmersionFactor A B f) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  let e := relativeOpenImmersionRangeIso B f
  have hc := openAffineWeilRestrictionComparison_bijective A B Y f.left.opensRange T
  constructor
  · intro p q hpq
    apply affineWeilRestrictionComparison_injective A B X T
    apply (cancel_mono e.hom).mp
    exact (affineWeilRestrictionOpenImmersionFactor_comparison A B f T p).symm.trans
      ((congrArg (openAffineWeilRestrictionComparison A B Y f.left.opensRange T)
        hpq).trans (affineWeilRestrictionOpenImmersionFactor_comparison A B f T q))
  · intro q
    obtain ⟨p, hp⟩ := affineWeilRestrictionComparison_surjective A B X T
      (openAffineWeilRestrictionComparison A B Y f.left.opensRange T q ≫ e.inv)
    refine ⟨p, hc.1 ?_⟩
    rw [affineWeilRestrictionOpenImmersionFactor_comparison, hp]
    change (_ ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- An explicit identification of the affine Weil restriction of the source
with the actual representing open subscheme in the target's restriction. -/
def affineWeilRestrictionOpenImmersionIso :
    affineWeilRestriction A B X ≅
      openAffineWeilRestriction A B Y f.left.opensRange :=
  asIso (affineWeilRestrictionOpenImmersionFactor A B f)

/-- The existing coordinate morphism of affine Weil restrictions is an actual
open immersion whenever the original morphism is an open immersion. -/
theorem affineWeilRestrictionMap_isOpenImmersion :
    IsOpenImmersion (affineWeilRestrictionMap A B f).left := by
  let g := affineWeilRestrictionOpenImmersionFactor A B f
  let : IsIso g.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of A))).map g))
  rw [← affineWeilRestrictionOpenImmersionFactor_fac A B f]
  change IsOpenImmersion
    (g.left ≫ (affineWeilRestrictionOpenLocus A B Y f.left.opensRange).ι)
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology
