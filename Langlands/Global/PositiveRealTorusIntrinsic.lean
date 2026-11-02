import Langlands.Global.PositiveRealTorus

/-!
# Intrinsic positive-real subgroups and their actual images

For a split torus, requiring every character to be a positive scalar idele
recovers the coordinate construction and proves independence of the splitting.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (F : Type u) [Field F]

/-- The actual map of affine point groups induced by a group-scheme homomorphism. -/
def pointMap
    (G H : GroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] (f : G ⟶ H) :
    Lie.AffinePoints G A →* Lie.AffinePoints H A :=
  ((GroupScheme.pointsMap f).app
    (op ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F A))))).hom

@[simp]
theorem pointMap_apply
    (G H : GroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] (f : G ⟶ H)
    (g : Lie.AffinePoints G A) :
    pointMap F G H A f g = g ≫ f.hom.hom := rfl

/-- Actual character evaluation, bundled as a homomorphism of affine point groups. -/
def characterHom (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] (χ : characterLattice T) :
    Lie.AffinePoints T.toGrp A →* Aˣ :=
  (Gm.affinePointsEquiv
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F A))).hom).toMonoidHom.comp
      (pointMap F T.toGrp (Gm (Spec (CommRingCat.of F))).toGrp A
        (CommGroupScheme.groupHom χ))

@[simp]
theorem characterHom_apply (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] (χ : characterLattice T)
    (g : Lie.AffinePoints T.toGrp A) :
    characterHom F T A χ g = Lie.characterValue χ g := rfl

variable (I : Type u) [Fintype I]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The actual character corresponding to one coordinate in a supplied splitting. -/
def coordinateCharacter (i : I) : characterLattice T :=
  Additive.ofMul
    (e.hom ≫ CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of F)) I i))

theorem characterValue_coordinateCharacter
    (A : Type u) [CommRing A] [Algebra F A]
    (g : Lie.AffinePoints T.toGrp A) (i : I) :
    Lie.characterValue (coordinateCharacter F I T e i) g =
      coordinates F I T e A g i := by
  unfold Lie.characterValue coordinateCharacter coordinates
  change Gm.affinePointsEquiv _ (g ≫
    (e.hom ≫ CommGroupScheme.groupHom
      (splitTorus.proj (Spec (CommRingCat.of F)) I i)).hom.hom) =
    Gm.affinePointsEquiv _ ((g ≫ e.hom.hom.hom) ≫
      (CommGroupScheme.groupHom
        (splitTorus.proj (Spec (CommRingCat.of F)) I i)).hom.hom)
  rw [Category.assoc]
  rfl

variable [NumberField F]

/-- The positive scalar subgroup of the actual full ideles. -/
def scalarSubgroup : Subgroup (Ideles F) :=
  (PositiveRealIdeles.full F).toMonoidHom.range

/-- Points whose every actual character is a positive scalar idele. -/
def intrinsicSubgroup : Subgroup (Lie.AffinePoints T.toGrp (Adeles F)) :=
  ⨅ χ : characterLattice T,
    (scalarSubgroup F).comap (characterHom F T (Adeles F) χ)

theorem mem_intrinsicSubgroup_iff (g : Lie.AffinePoints T.toGrp (Adeles F)) :
    g ∈ intrinsicSubgroup F T ↔
      ∀ χ : characterLattice T, ∃ x, PositiveRealIdeles.full F x =
        Lie.characterValue χ g := by
  simp only [intrinsicSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap,
    characterHom_apply]
  rfl

/-- For a supplied splitting, the intrinsic and coordinate subgroups agree. -/
theorem subgroup_eq_intrinsicSubgroup :
    subgroup F I T e = intrinsicSubgroup F T := by
  classical
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    apply (mem_intrinsicSubgroup_iff F T _).mpr
    intro χ
    exact ⟨positiveCharacter F I T e χ x, (characterValue_full F I T e χ x).symm⟩
  · intro hg
    have hc := (mem_intrinsicSubgroup_iff F T g).mp hg
    choose x hx using fun i => hc (coordinateCharacter F I T e i)
    apply (mem_subgroup_iff F I T e g).mpr
    refine ⟨x, (coordinates F I T e (Adeles F)).injective ?_⟩
    rw [coordinates_full]
    funext i
    exact (hx i).trans (characterValue_coordinateCharacter F I T e (Adeles F) g i)

/-- The positive-real subgroup does not depend on the finite coordinates or splitting. -/
theorem subgroup_eq_of_splittings
    (J : Type u) [Fintype J]
    (e' : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J) :
    subgroup F I T e = subgroup F J T e' := by
  rw [subgroup_eq_intrinsicSubgroup, subgroup_eq_intrinsicSubgroup]

/-- Actual homomorphisms carry the intrinsic positive subgroup into the target's. -/
theorem map_intrinsicSubgroup_le
    (T' : CommGroupScheme (Spec (CommRingCat.of F))) (f : T ⟶ T') :
    (intrinsicSubgroup F T).map
        (pointMap F T.toGrp T'.toGrp (Adeles F) (CommGroupScheme.groupHom f)) ≤
      intrinsicSubgroup F T' := by
  rintro _ ⟨g, hg, rfl⟩
  apply (mem_intrinsicSubgroup_iff F T' _).mpr
  intro χ
  have h := (mem_intrinsicSubgroup_iff F T g).mp hg (f ≫ χ)
  rw [Lie.characterValue_comp] at h
  exact h

/-- The actual positive-real image in an arbitrary ambient group scheme. -/
def imageSubgroup (G : GroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) :
    Subgroup (Lie.AffinePoints G (Adeles F)) :=
  (intrinsicSubgroup F T).map (pointMap F T.toGrp G (Adeles F) i)

/-- A supplied splitting computes the same ambient image subgroup. -/
theorem imageSubgroup_eq_map
    (G : GroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) :
    imageSubgroup F T G i =
      (subgroup F I T e).map (pointMap F T.toGrp G (Adeles F) i) := by
  rw [subgroup_eq_intrinsicSubgroup]
  rfl

end Langlands.Global.PositiveRealTorus
