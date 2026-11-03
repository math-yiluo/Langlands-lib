import Langlands.AlgebraicGeometry.SchemeLimitModelMaps
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # The actual colimit comparison for relative model morphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

variable {I : Type u} [SmallCategory I]
  (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (a : X ⟶ S) (b : Y ⟶ S)

/-- The actual relative Hom sets, covariant on the opposite base index. -/
def homFunctor : Iᵒᵖ ⥤ Type u where
  obj i := LevelHom D t a b i.unop
  map r := ↾(restrict D t a b r.unop)
  map_id i := by
    ext f
    exact restrict_id D t a b i.unop f
  map_comp r s := by
    ext f
    exact (restrict_comp D t a b s.unop r.unop f).symm

/-- The type colimit of actual relative morphisms between the level models. -/
def HomColimit : Type u := (homFunctor D t a b).ColimitType

/-- The class of an actual relative morphism at a level. -/
def homColimitι (i : I) : LevelHom D t a b i → HomColimit D t a b :=
  (homFunctor D t a b).ιColimitType (op i)

/-- Restricting a level morphism preserves its colimit class. -/
@[simp]
lemma homColimitι_restrict {i j : I} (r : i ⟶ j) (f : LevelHom D t a b j) :
    homColimitι D t a b i (restrict D t a b r f) = homColimitι D t a b j f :=
  (homFunctor D t a b).ιColimitType_map r.op f

/-- Every colimit element has an actual level representative. -/
lemma homColimitι_jointly_surjective (z : HomColimit D t a b) :
    ∃ (i : I) (f : LevelHom D t a b i), homColimitι D t a b i f = z := by
  obtain ⟨i, f, hf⟩ := (homFunctor D t a b).ιColimitType_jointly_surjective z
  exact ⟨i.unop, f, hf⟩

variable (c : Cone D) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

/-- The type cocone whose legs are actual base change to the supplied cone base. -/
def homCoconeTypes : (homFunctor D t a b).CoconeTypes where
  pt := LimitHom a b p
  ι i := toLimit D t a b c p hp i.unop
  ι_naturality r := by
    funext f
    exact toLimit_restrict D t a b c p hp r.unop f

/-- The same actual base-change cocone as a categorical cocone of types. -/
def homCocone : Cocone (homFunctor D t a b) :=
  (homFunctor D t a b).coconeTypesEquiv (homCoconeTypes D t a b c p hp)

@[simp]
lemma homCocone_ι_app (i : I) (f : LevelHom D t a b i) :
    (homCocone D t a b c p hp).ι.app (op i) f = toLimit D t a b c p hp i f := rfl

/-- The canonical comparison from the actual Hom colimit to morphisms over the
supplied cone base. No limit witness or finiteness assumption is used here. -/
def homColimitMap : HomColimit D t a b → LimitHom a b p :=
  (homFunctor D t a b).descColimitType (homCoconeTypes D t a b c p hp)

/-- The canonical comparison is actual base change on every representative. -/
@[simp]
lemma homColimitMap_ι (i : I) (f : LevelHom D t a b i) :
    homColimitMap D t a b c p hp (homColimitι D t a b i f) =
      toLimit D t a b c p hp i f := rfl

end Langlands.AlgebraicGeometry.SchemeLimitModel
