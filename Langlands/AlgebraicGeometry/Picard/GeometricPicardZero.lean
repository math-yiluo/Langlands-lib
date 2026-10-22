import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Translation invariance on geometric fibres -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Left translation by a section, constructed with the actual group law. -/
def translation (x : Over.mk (𝟙 S) ⟶ G.X) : G.X ⟶ G.X :=
  (Over.mkIdTerminal.from G.X ≫ x) * 𝟙 G.X

/-- Translation acts on every test scheme by multiplication by the restricted section. -/
lemma points_translation (x : Over.mk (𝟙 S) ⟶ G.X) (T : Over S) (y : T ⟶ G.X) :
    y ≫ translation G x = (Over.mkIdTerminal.from T ≫ x) * y := by
  rw [translation, MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  rw [Over.mkIdTerminal.hom_ext (y ≫ Over.mkIdTerminal.from G.X)
    (Over.mkIdTerminal.from T)]

/-- Translation by the identity section is the identity morphism. -/
@[simp] lemma translation_one : translation G 1 = 𝟙 G.X := by
  simp [translation]

/-- A line bundle is invariant under translation by every section over the base. -/
def IsTranslationInvariant
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left) : Prop :=
  ∀ x : Over.mk (𝟙 S) ⟶ G.X,
    Nonempty ((Langlands.AlgebraicGeometry.Picard.LineBundle.pullback
      (translation G x).left).obj L ≅ L)

open Langlands.AlgebraicGeometry.Picard

/-- Translation invariance depends only on the isomorphism class of the line bundle. -/
lemma isTranslationInvariant_of_iso {L M : LineBundle G.X.left} (e : L ≅ M)
    (hL : IsTranslationInvariant G L) : IsTranslationInvariant G M := by
  intro x
  obtain ⟨a⟩ := hL x
  exact ⟨(LineBundle.pullback (translation G x).left).mapIso e.symm ≪≫ a ≪≫ e⟩

lemma isTranslationInvariant_iff_of_iso {L M : LineBundle G.X.left} (e : L ≅ M) :
    IsTranslationInvariant G L ↔ IsTranslationInvariant G M :=
  ⟨isTranslationInvariant_of_iso G e, isTranslationInvariant_of_iso G e.symm⟩

/-- The structure line bundle is translation invariant. -/
lemma isTranslationInvariant_trivial : IsTranslationInvariant G (LineBundle.trivial G.X.left) :=
  fun x ↦ ⟨LineBundle.pullbackTrivialIso (translation G x).left⟩

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Restrict a line bundle to the actual base change of the abelian scheme. -/
def fibreLineBundle (L : LineBundle A.X.left) {T : Scheme.{u}} (s : T ⟶ S) :
    LineBundle ((baseChange s).obj A).X.left :=
  (LineBundle.pullback (pullback.fst A.X.hom s)).obj L

/-- The geometric-fibre Picard-zero condition, expressed by translation invariance. -/
def IsGeometricallyPicardZero (L : LineBundle A.X.left) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
    GroupScheme.IsTranslationInvariant ((baseChange s).obj A).toGrp (fibreLineBundle A L s)

/-- The geometric-fibre condition is unchanged by isomorphism of line bundles. -/
lemma isGeometricallyPicardZero_of_iso {L M : LineBundle A.X.left} (e : L ≅ M)
    (hL : IsGeometricallyPicardZero A L) : IsGeometricallyPicardZero A M := by
  intro K _ _ s
  exact GroupScheme.isTranslationInvariant_of_iso _
    ((LineBundle.pullback (pullback.fst A.X.hom s)).mapIso e) (hL K s)

lemma isGeometricallyPicardZero_iff_of_iso {L M : LineBundle A.X.left} (e : L ≅ M) :
    IsGeometricallyPicardZero A L ↔ IsGeometricallyPicardZero A M :=
  ⟨isGeometricallyPicardZero_of_iso A e, isGeometricallyPicardZero_of_iso A e.symm⟩

/-- The structure line bundle satisfies the geometric-fibre Picard-zero condition. -/
lemma isGeometricallyPicardZero_trivial :
    IsGeometricallyPicardZero A (LineBundle.trivial A.X.left) := by
  intro K _ _ s
  exact GroupScheme.isTranslationInvariant_of_iso _
    (LineBundle.pullbackTrivialIso (pullback.fst A.X.hom s)).symm
    (GroupScheme.isTranslationInvariant_trivial _)

end Langlands.AbelianScheme
