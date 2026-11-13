import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Base change of the relative Picard class sheaf

For `f : X ⟶ S` and `g : S' ⟶ S`, the fibre product `T ×_{S'} (X ×_S S')` of a scheme `T`
over `S'` is canonically `T ×_S X`. Hence the relative Picard class presheaf of the base
change `X ×_S S' ⟶ S'` is the restriction of that of `f` along `Over.map g`. Since
`Over.map g` is continuous and cocontinuous for the fppf topologies, restriction commutes
with fppf sheafification, and the same identification holds for the fppf class sheaves.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S S' X : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

@[reassoc]
lemma relativeSpace_map_fst {T U : Over S} (h : T ⟶ U) :
    (relativeSpace f).map h ≫ pullback.fst U.hom f = pullback.fst T.hom f ≫ h.left :=
  pullback.lift_fst _ _ _

/-- The pasted square exhibiting `T ×_{S'} (X ×_S S')` as `T ×_S X`. -/
lemma relativeSpace_baseChange_isPullback (T : Over S') :
    IsPullback (pullback.fst T.hom (pullback.snd f g))
      (pullback.snd T.hom (pullback.snd f g) ≫ pullback.fst f g) (T.hom ≫ g) f :=
  (IsPullback.of_hasPullback T.hom (pullback.snd f g)).paste_vert
    (IsPullback.of_hasPullback f g).flip

/-- The fibre-product family of a base change is the restriction of the original family. -/
def relativeSpaceBaseChangeIso :
    relativeSpace (pullback.snd f g) ≅ Over.map g ⋙ relativeSpace f :=
  NatIso.ofComponents (fun T ↦ (relativeSpace_baseChange_isPullback f g T).isoPullback)
    fun {T U} h ↦ by
      have hT := relativeSpace_baseChange_isPullback f g T
      have hU := relativeSpace_baseChange_isPullback f g U
      apply pullback.hom_ext <;> simp only [Category.assoc]
      · calc _ = (relativeSpace (pullback.snd f g)).map h ≫
                pullback.fst U.hom (pullback.snd f g) :=
              (relativeSpace (pullback.snd f g)).map h ≫= hU.isoPullback_hom_fst
          _ = pullback.fst T.hom (pullback.snd f g) ≫ h.left := relativeSpace_map_fst _ h
          _ = hT.isoPullback.hom ≫ pullback.fst (T.hom ≫ g) f ≫ h.left :=
              (hT.isoPullback_hom_fst_assoc h.left).symm
          _ = _ := hT.isoPullback.hom ≫= (relativeSpace_map_fst f ((Over.map g).map h)).symm
      · calc _ = (relativeSpace (pullback.snd f g)).map h ≫
                pullback.snd U.hom (pullback.snd f g) ≫ pullback.fst f g :=
              (relativeSpace (pullback.snd f g)).map h ≫= hU.isoPullback_hom_snd
          _ = pullback.snd T.hom (pullback.snd f g) ≫ pullback.fst f g :=
              relativeSpace_map_snd_assoc _ h _
          _ = hT.isoPullback.hom ≫ pullback.snd (T.hom ≫ g) f := hT.isoPullback_hom_snd.symm
          _ = _ := hT.isoPullback.hom ≫= (relativeSpace_map_snd f ((Over.map g).map h)).symm

namespace RelativePicard

/-- The relative Picard class presheaf of a base change is the restriction of the original
class presheaf along `Over.map g`. -/
def classPresheafBaseChangeIso :
    classPresheaf (pullback.snd f g) ≅ (Over.map g).op ⋙ classPresheaf f :=
  Functor.isoWhiskerRight (NatIso.op (relativeSpaceBaseChangeIso f g).symm)
    (Group.functor ⋙ forget AddCommGrpCat)

/-- The fppf relative Picard class sheaf of a base change is the restriction of the original
class sheaf along `Over.map g`. -/
def classSheafBaseChangeIso :
    classSheaf (pullback.snd f g) ≅
      (Over.map g).sheafPushforwardContinuous (Type (u + 1)) (Scheme.fppfTopology.over S')
        (Scheme.fppfTopology.over S) |>.obj (classSheaf f) :=
  (presheafToSheaf _ _).mapIso (classPresheafBaseChangeIso f g) ≪≫
    ((Over.map g).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app (classPresheaf f)

/-- The underlying presheaf form of `classSheafBaseChangeIso`. -/
def classSheafPresheafBaseChangeIso :
    classSheafPresheaf (pullback.snd f g) ≅ (Over.map g).op ⋙ classSheafPresheaf f :=
  (sheafToPresheaf _ _).mapIso (classSheafBaseChangeIso f g)

end RelativePicard

end Langlands.AlgebraicGeometry.Picard
