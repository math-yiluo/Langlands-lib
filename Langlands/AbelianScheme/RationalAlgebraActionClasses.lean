import Langlands.AbelianScheme.RationalAlgebraAction
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # Isomorphism classes of actual rational algebra actions -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite

universe u v

namespace Langlands.AbelianScheme.RationalAlgebraAction

variable {S S' S'' : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D]

/-- Actual abelian schemes with rational algebra action, up to actual
equivariant rational isomorphism. -/
abbrev IsoClass (S : Scheme.{u}) (D : Type v) [Ring D] [Algebra ℚ D] :=
  Quotient (isIsomorphicSetoid (RationalAlgebraAction S D))

/-- The class of an actual abelian scheme and its rational algebra action. -/
def classOf (X : RationalAlgebraAction S D) : IsoClass S D :=
  Quotient.mk _ X

/-- Equality of classes means an actual equivariant rational isomorphism exists. -/
theorem classOf_eq_iff {X Y : RationalAlgebraAction S D} :
    classOf X = classOf Y ↔ Nonempty (X ≅ Y) :=
  Quotient.eq

/-- The quotient relation retains the actual rational inverse and the action equation. -/
theorem classOf_eq_iff_rationalIso {X Y : RationalAlgebraAction S D} :
    classOf X = classOf Y ↔
      ∃ e : Rationalization.of X.abelianScheme ≅ Rationalization.of Y.abelianScheme,
        ∀ d : D, comp0 _ _ _ (X.action d) e.hom =
          comp0 _ _ _ e.hom (Y.action d) := by
  rw [classOf_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨underlyingIso e, intertwines e.hom⟩
  · rintro ⟨e, he⟩
    exact ⟨isoMk e he⟩

/-- Every class has an actual abelian-scheme representative with its actual action. -/
theorem classOf_surjective : Function.Surjective (classOf (S := S) (D := D)) :=
  Quotient.mk_surjective

/-- Actual geometric pullback descends to rational equivariant isomorphism classes. -/
def pullbackClass (b : S' ⟶ S) : IsoClass S D → IsoClass S' D :=
  Quotient.map (pullback b).obj (by
    intro X Y h
    rcases h with ⟨e⟩
    exact ⟨(pullback b).mapIso e⟩)

@[simp] theorem pullbackClass_classOf (b : S' ⟶ S) (X : RationalAlgebraAction S D) :
    pullbackClass b (classOf X) = classOf ((pullback b).obj X) := rfl

/-- The actual identity comparison gives the identity law after quotienting. -/
@[simp] theorem pullbackClass_id (q : IsoClass S D) :
    pullbackClass (𝟙 S) q = q := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_eq_iff.mpr ⟨pullbackIdIso X⟩

/-- The actual binary comparison gives strict composition on isomorphism classes. -/
theorem pullbackClass_comp (b : S' ⟶ S) (c : S'' ⟶ S') (q : IsoClass S D) :
    pullbackClass (c ≫ b) q = pullbackClass c (pullbackClass b q) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_eq_iff.mpr ⟨pullbackCompIso b c X⟩

/-- The presheaf of actual rational algebra-action isomorphism classes. -/
def isoClassPresheaf (D : Type v) [Ring D] [Algebra ℚ D] :
    Scheme.{u}ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj S := IsoClass S.unop D
  map b := ↾(pullbackClass (D := D) b.unop)
  map_id S := by
    ext q
    exact pullbackClass_id q
  map_comp b c := by
    ext q
    exact pullbackClass_comp b.unop c.unop q

@[simp] theorem isoClassPresheaf_obj (S : Scheme.{u}) :
    (isoClassPresheaf D).obj (op S) = IsoClass S D := rfl

@[simp] theorem isoClassPresheaf_map_classOf (b : S' ⟶ S)
    (X : RationalAlgebraAction S D) :
    (isoClassPresheaf D).map b.op (classOf X) =
      classOf ((pullback b).obj X) := rfl

/-- Restrict the actual presheaf to schemes over a fixed base, such as a reflex field. -/
def isoClassOverPresheaf (E : Scheme.{u}) (D : Type v) [Ring D] [Algebra ℚ D] :
    (Over E)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  (Over.forget E).op ⋙ isoClassPresheaf D

@[simp] theorem isoClassOverPresheaf_obj (E : Scheme.{u}) (T : Over E) :
    (isoClassOverPresheaf E D).obj (op T) = IsoClass T.left D := rfl

@[simp] theorem isoClassOverPresheaf_map_classOf {E : Scheme.{u}}
    {T T' : Over E} (b : T' ⟶ T) (X : RationalAlgebraAction T.left D) :
    (isoClassOverPresheaf E D).map b.op (classOf X) =
      classOf ((pullback b.left).obj X) := rfl

/-- Changing the fixed base restricts the same actual moduli presheaf. -/
def isoClassOverPresheafBaseIso {E E' : Scheme.{u}} (a : E' ⟶ E) :
    (Over.map a).op ⋙ isoClassOverPresheaf E D ≅ isoClassOverPresheaf E' D :=
  Iso.refl _

end Langlands.AbelianScheme.RationalAlgebraAction
