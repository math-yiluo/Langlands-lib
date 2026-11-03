import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent

/-! # Actual morphisms between models at a level and at a limit -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open EtaleEquivalenceRelation.Action.TargetLimit
open AffineLimit

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (a : X ⟶ S) (b : Y ⟶ S)

/-- Actual morphisms between the two base-changed models over a level. -/
def LevelHom (i : I) :=
  {f : (diagram D t a).obj i ⟶ (diagram D t b).obj i //
    f ≫ pullback.fst (t.app i) b = pullback.fst (t.app i) a}

/-- Actual morphisms between the two models over a supplied limit base. -/
def LimitHom {T : Scheme.{u}} (p : T ⟶ S) :=
  {f : pullback p a ⟶ pullback p b //
    f ≫ pullback.fst p b = pullback.fst p a}

/-- Restrict a level morphism along a transition of the base diagram. -/
noncomputable def restrict {i j : I} (r : i ⟶ j)
    (f : LevelHom D t a b j) : LevelHom D t a b i :=
  ⟨pullback.lift (pullback.fst (t.app i) a)
    ((diagram D t a).map r ≫ f.val ≫ pullback.snd (t.app j) b) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition,
        ← Category.assoc f.val, f.property, diagram_map_fst_assoc]
      simp [Over.lift]),
    pullback.lift_fst _ _ _⟩

@[reassoc (attr := simp)]
lemma restrict_fst {i j : I} (r : i ⟶ j) (f : LevelHom D t a b j) :
    (restrict D t a b r f).val ≫ pullback.fst (t.app i) b =
      pullback.fst (t.app i) a :=
  (restrict D t a b r f).property

@[reassoc (attr := simp)]
lemma restrict_snd {i j : I} (r : i ⟶ j) (f : LevelHom D t a b j) :
    (restrict D t a b r f).val ≫ pullback.snd (t.app i) b =
      (diagram D t a).map r ≫ f.val ≫ pullback.snd (t.app j) b :=
  pullback.lift_snd _ _ _

/-- Restriction is characterized by its actual transition square. -/
lemma restrict_square {i j : I} (r : i ⟶ j) (f : LevelHom D t a b j) :
    (diagram D t a).map r ≫ f.val =
      (restrict D t a b r f).val ≫ (diagram D t b).map r := by
  apply pullback.hom_ext
  · simp [f.property]
  · simp

@[simp]
lemma restrict_id (i : I) (f : LevelHom D t a b i) :
    restrict D t a b (𝟙 i) f = f := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [f.property]
  · simp

@[simp]
lemma restrict_comp {i j k : I} (r : i ⟶ j) (s : j ⟶ k)
    (f : LevelHom D t a b k) :
    restrict D t a b r (restrict D t a b s f) =
      restrict D t a b (r ≫ s) f := by
  apply Subtype.ext
  apply pullback.hom_ext <;> simp

variable (c : Cone D) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

/-- Restrict a level morphism to the supplied limit base. No limit witness
or finiteness assumption is needed for this actual base-change map. -/
noncomputable def toLimit (i : I) (f : LevelHom D t a b i) :
    LimitHom a b p :=
  ⟨pullback.lift (pullback.fst p a)
    ((cone D t a c p hp).π.app i ≫ f.val ≫ pullback.snd (t.app i) b) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition,
        ← Category.assoc f.val, f.property, cone_π_fst_assoc, hp i]),
    pullback.lift_fst _ _ _⟩

@[reassoc (attr := simp)]
lemma toLimit_fst (i : I) (f : LevelHom D t a b i) :
    (toLimit D t a b c p hp i f).val ≫ pullback.fst p b = pullback.fst p a :=
  (toLimit D t a b c p hp i f).property

@[reassoc (attr := simp)]
lemma toLimit_snd (i : I) (f : LevelHom D t a b i) :
    (toLimit D t a b c p hp i f).val ≫ pullback.snd p b =
      (cone D t a c p hp).π.app i ≫ f.val ≫ pullback.snd (t.app i) b :=
  pullback.lift_snd _ _ _

/-- The limit morphism has the prescribed base-change square. -/
lemma toLimit_square (i : I) (f : LevelHom D t a b i) :
    (cone D t a c p hp).π.app i ≫ f.val =
      (toLimit D t a b c p hp i f).val ≫ (cone D t b c p hp).π.app i := by
  apply pullback.hom_ext
  · simp [f.property]
  · simp

@[simp]
lemma toLimit_restrict {i j : I} (r : i ⟶ j) (f : LevelHom D t a b j) :
    toLimit D t a b c p hp i (restrict D t a b r f) =
      toLimit D t a b c p hp j f := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp
  · simp [← Category.assoc]

end Langlands.AlgebraicGeometry.SchemeLimitModel
