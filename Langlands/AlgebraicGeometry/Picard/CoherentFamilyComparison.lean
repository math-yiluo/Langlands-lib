import Langlands.AlgebraicGeometry.Picard.CoherentFamilyInclusion
import Langlands.AlgebraicGeometry.Picard.ModuleComparison
import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback

/-! # The actual Picard inclusion as a strong transformation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open CoherentSheaves

variable {X S : Scheme.{u}}

private def propertyStrongTrans {C : Type*} [Category* C]
    {F G : LocallyDiscrete C ⥤ᵖ Cat} (α : Pseudofunctor.StrongTrans F G)
    (P : G.ObjectProperty) [P.IsClosedUnderMapObj]
    (hP : ∀ (a : LocallyDiscrete C) (L : F.obj a), P.prop a ((α.app a).toFunctor.obj L)) :
    Pseudofunctor.StrongTrans F P.fullsubcategory where
  app a := ((P.prop a).lift (α.app a).toFunctor (hP a)).toCatHom
  naturality {a b} h := Cat.Hom.isoMk (NatIso.ofComponents
    (fun L => ObjectProperty.isoMk _ ((Cat.Hom.toNatIso (α.naturality h)).app L))
    (fun t => by
      apply ObjectProperty.hom_ext
      exact (α.naturality h).hom.toNatTrans.naturality t))
  naturality_naturality η := by
    obtain rfl := obj_ext_of_isDiscrete η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst hη
    simp only [PrelaxFunctor.map₂_id, id_whiskerRight,
      whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    apply ObjectProperty.hom_ext
    exact congrArg (fun η => η.toNatTrans.app L) (α.naturality_id a)
  naturality_comp h k := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    apply ObjectProperty.hom_ext
    exact congrArg (fun η => η.toNatTrans.app L) (α.naturality_comp h k)

private def groupoidLift {C D : Type*} [Category* C] [IsGroupoid C] [Category* D]
    (F : C ⥤ D) : C ⥤ Core D := by
  letI := Groupoid.ofIsGroupoid (C := C)
  exact Core.functorToCore F

private def coreStrongTrans {C : Type*} [Category* C]
    {F G : LocallyDiscrete C ⥤ᵖ Cat} [∀ a, IsGroupoid (F.obj a)]
    (α : Pseudofunctor.StrongTrans F G) :
    Pseudofunctor.StrongTrans F (corePseudofunctor G) where
  app a := (groupoidLift (α.app a).toFunctor).toCatHom
  naturality {a b} h := Cat.Hom.isoMk (NatIso.ofComponents
    (fun L => Core.isoMk ((Cat.Hom.toNatIso (α.naturality h)).app L))
    (fun t => by
      apply Core.hom_ext
      exact (α.naturality h).hom.toNatTrans.naturality t))
  naturality_naturality η := by
    obtain rfl := obj_ext_of_isDiscrete η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst hη
    simp only [PrelaxFunctor.map₂_id, id_whiskerRight,
      whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    apply Core.hom_ext
    exact congrArg (fun η => η.toNatTrans.app L) (α.naturality_id a)
  naturality_comp h k := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    apply Core.hom_ext
    exact congrArg (fun η => η.toNatTrans.app L) (α.naturality_comp h k)

private def replaceStrongTransApp {B : Type*} [Bicategory B]
    {F G : B ⥤ᵖ Cat} (α : Pseudofunctor.StrongTrans F G)
    (A : ∀ a, F.obj a ⟶ G.obj a) (hA : ∀ a, α.app a = A a) :
    Pseudofunctor.StrongTrans F G where
  app := A
  naturality {a b} h :=
    eqToIso (congrArg (fun p => F.map h ≫ p) (hA b).symm) ≪≫
      α.naturality h ≪≫ eqToIso (congrArg (fun p => p ≫ G.map h) (hA a))
  naturality_naturality η := by
    have e : A = α.app := (funext hA).symm
    subst A
    simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using α.naturality_naturality η
  naturality_id a := by
    have e : A = α.app := (funext hA).symm
    subst A
    simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using α.naturality_id a
  naturality_comp h k := by
    have e : A = α.app := (funext hA).symm
    subst A
    simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using α.naturality_comp h k

private def toFamilyCategoryStrongTrans (f : X ⟶ S) [Flat f] :
    Pseudofunctor.StrongTrans
      ((relativeSpace f).op.toPseudofunctor.comp pseudofunctor)
      (Family.pseudofunctor f) :=
  propertyStrongTrans (toModuleStrongTrans (relativeSpace f).op) (familyProperty f)
    (fun T L => ((relativeToFamily f T.as.unop).obj L).of.property)

private instance relativeIsGroupoid (f : X ⟶ S) (T : LocallyDiscrete (Over S)ᵒᵖ) :
    IsGroupoid (((relativeSpace f).op.toPseudofunctor.comp pseudofunctor).obj T) := by
  change IsGroupoid (PicardGroupoid ((relativeSpace f).obj T.as.unop))
  infer_instance

/-- The actual Picard inclusion commutes with ordinary family pullback,
including the identity and composition comparisons on the full slice. -/
private def toFamilyStrongTransAux (f : X ⟶ S) [Flat f] :
    Pseudofunctor.StrongTrans
      ((relativeSpace f).op.toPseudofunctor.comp pseudofunctor)
      (FamilyGroupoid.pseudofunctor f) :=
  coreStrongTrans (toFamilyCategoryStrongTrans f)

private lemma toFamilyStrongTransAux_app (f : X ⟶ S) [Flat f] (T : Over S) :
    ((toFamilyStrongTransAux f).app (.mk (op T))).toFunctor = relativeToFamily f T := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro L
    rfl
  case h_map =>
    intro L M a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- The actual relative Picard inclusion as a strong transformation to the
actual coherent-family groupoids, on the full slice over the base scheme. -/
def toFamilyStrongTrans (f : X ⟶ S) [Flat f] :
    Pseudofunctor.StrongTrans
      ((relativeSpace f).op.toPseudofunctor.comp pseudofunctor)
      (FamilyGroupoid.pseudofunctor f) :=
  replaceStrongTransApp (toFamilyStrongTransAux f)
    (fun T => (relativeToFamily f T.as.unop).toCatHom)
    (fun T => by
      apply Cat.Hom.ext
      exact toFamilyStrongTransAux_app f T.as.unop)

@[simp]
theorem toFamilyStrongTrans_app (f : X ⟶ S) [Flat f] (T : Over S) :
    ((toFamilyStrongTrans f).app (.mk (op T))).toFunctor = relativeToFamily f T := rfl

/-- Every component of the strong transformation is fully faithful. -/
def toFamilyStrongTransFullyFaithful (f : X ⟶ S) [Flat f] (T : Over S) :
    (((toFamilyStrongTrans f).app (.mk (op T))).toFunctor).FullyFaithful :=
  relativeToFamilyFullyFaithful f T

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
