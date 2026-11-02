import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # The family of base changes of a scheme with a section -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S X : Scheme.{u}}

/-- The family `T ↦ T ×_S X`, reusing the slice-category pullback functor. -/
abbrev relativeSpace (f : X ⟶ S) : Over S ⥤ Scheme.{u} :=
  Over.pullback f ⋙ Over.forget X

@[reassoc]
lemma relativeSpace_map_snd (f : X ⟶ S) {T U : Over S} (h : T ⟶ U) :
    (relativeSpace f).map h ≫ pullback.snd U.hom f = pullback.snd T.hom f :=
  pullback.lift_snd _ _ _

/-- The natural projection from `T ×_S X` to `T`. -/
def relativeProjection (f : X ⟶ S) : relativeSpace f ⟶ Over.forget S where
  app T := pullback.fst T.hom f
  naturality {T U} h := by simp [relativeSpace, Over.pullback, pullback.lift_fst]

/-- The section induced on every base change of a scheme with a section. -/
def relativeSection (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S) :
    Over.forget S ⟶ relativeSpace f where
  app T := pullback.lift (𝟙 T.left) (T.hom ≫ ε) (by simp [section_eq])
  naturality {T U} h := by
    apply pullback.hom_ext
    · simp [relativeSpace, Over.pullback, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
        Category.assoc, pullback.lift_snd, Over.w_assoc]

@[simp]
lemma relativeSection_projection (f : X ⟶ S) (ε : S ⟶ X)
    (section_eq : ε ≫ f = 𝟙 S) (T : Over S) :
    (relativeSection f ε section_eq).app T ≫ (relativeProjection f).app T = 𝟙 T.left := by
  exact pullback.lift_fst _ _ _

@[simp]
lemma relativeSection_snd (f : X ⟶ S) (ε : S ⟶ X)
    (section_eq : ε ≫ f = 𝟙 S) (T : Over S) :
    (relativeSection f ε section_eq).app T ≫ pullback.snd T.hom f = T.hom ≫ ε := by
  exact pullback.lift_snd _ _ _

/-- The chosen fibre product is canonically the more usual `X ×_S T`. -/
def relativeSpaceSymmetry (f : X ⟶ S) (T : Over S) :
    (relativeSpace f).obj T ≅ pullback f T.hom :=
  pullbackSymmetry T.hom f

end Langlands.AlgebraicGeometry.Picard
