import Langlands.AlgebraicGeometry.CoherentSheaves.Groupoid
import Langlands.AlgebraicGeometry.Modules.FinitePresentationPullback
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessPullback
import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Ordinary pullback of flat finitely presented families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

private lemma cat_pseudofunctor_associativity {C : Type*} [Category* C]
    (F : LocallyDiscrete C ⥤ᵖ Cat) {T U V W : C}
    (h : T ⟶ U) (k : U ⟶ V) (l : V ⟶ W) :
    (Cat.Hom.toNatIso (F.mapComp (h ≫ k).toLoc l.toLoc)).hom ≫
      Functor.whiskerRight (Cat.Hom.toNatIso (F.mapComp h.toLoc k.toLoc)).hom _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (Cat.Hom.toNatIso (F.mapComp k.toLoc l.toLoc)).inv ≫
            (Cat.Hom.toNatIso (F.mapComp h.toLoc (k ≫ l).toLoc)).inv =
      eqToHom (by simp) := by
  have hc := F.map₂_associator h.toLoc k.toLoc l.toLoc
  rw [Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom] at hc
  simpa only [Cat.Hom.toNatIso, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans,
    Cat.whiskerLeft_toNatTrans, Cat.associator_hom_toNatTrans,
    Quiver.Hom.comp_toLoc] using (congrArg Cat.Hom₂.toNatTrans hc).symm

private lemma cat_pseudofunctor_left_unitality {C : Type*} [Category* C]
    (F : LocallyDiscrete C ⥤ᵖ Cat) {T U : C} (h : T ⟶ U) :
    (Cat.Hom.toNatIso (F.mapComp (𝟙 T).toLoc h.toLoc)).hom ≫
      Functor.whiskerRight (Cat.Hom.toNatIso (F.mapId (.mk T))).hom
        (F.map h.toLoc).toFunctor ≫
          (Functor.leftUnitor _).hom = eqToHom (by simp) := by
  have hc := F.map₂_left_unitor h.toLoc
  rw [Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom] at hc
  simpa only [Cat.Hom.toNatIso, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans,
    Cat.leftUnitor_hom_toNatTrans, Quiver.Hom.comp_toLoc, Quiver.Hom.id_toLoc] using
    (congrArg Cat.Hom₂.toNatTrans hc).symm

private lemma cat_pseudofunctor_right_unitality {C : Type*} [Category* C]
    (F : LocallyDiscrete C ⥤ᵖ Cat) {T U : C} (h : T ⟶ U) :
    (Cat.Hom.toNatIso (F.mapComp h.toLoc (𝟙 U).toLoc)).hom ≫
      Functor.whiskerLeft (F.map h.toLoc).toFunctor
        (Cat.Hom.toNatIso (F.mapId (.mk U))).hom ≫
          (Functor.rightUnitor _).hom = eqToHom (by simp) := by
  have hc := F.map₂_right_unitor h.toLoc
  rw [Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom] at hc
  simpa only [Cat.Hom.toNatIso, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans,
    Cat.rightUnitor_hom_toNatTrans, Quiver.Hom.comp_toLoc, Quiver.Hom.id_toLoc] using
    (congrArg Cat.Hom₂.toNatTrans hc).symm

private lemma core_eqToHom {C : Type*} [Category* C] {A B : Core C} (e : A = B) :
    (eqToHom e).iso.hom = eqToHom (congrArg Core.of e) := by
  cases e
  rfl

private def corePseudofunctor {C : Type*} [Category* C]
    (F : LocallyDiscrete C ⥤ᵖ Cat) : LocallyDiscrete C ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun T ↦ Cat.of (Core (F.obj (.mk T))))
    (fun h ↦ ((F.map h.toLoc).toFunctor.core).toCatHom)
    (fun T ↦ Cat.Hom.isoMk (Cat.Hom.toNatIso (F.mapId (.mk T))).core)
    (fun h k ↦ Cat.Hom.isoMk (Cat.Hom.toNatIso (F.mapComp h.toLoc k.toLoc)).core)
    (fun h k l ↦ by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext M
      apply Core.hom_ext
      simpa [Functor.core, Core.functorToCore, Core.inclusion,
        eqToHom_app, core_eqToHom] using
        congrArg (fun η ↦ η.app M.of) (cat_pseudofunctor_associativity F h k l))
    (fun h ↦ by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext M
      apply Core.hom_ext
      simpa [Functor.core, Core.functorToCore, Core.inclusion,
        eqToHom_app, core_eqToHom] using
        congrArg (fun η ↦ η.app M.of) (cat_pseudofunctor_left_unitality F h))
    (fun h ↦ by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext M
      apply Core.hom_ext
      simpa [Functor.core, Core.functorToCore, Core.inclusion,
        eqToHom_app, core_eqToHom] using
        congrArg (fun η ↦ η.app M.of) (cat_pseudofunctor_right_unitality F h))

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The published ordinary module pullback pseudofunctor on the actual relative spaces. -/
def modulePseudofunctor : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat :=
  ((Picard.relativeSpace f).op.toPseudofunctor.comp Scheme.Modules.pseudofunctor).comp
    Adj.forget₁

/-- The family property in every category of actual relative-space modules. -/
def familyProperty : (modulePseudofunctor f).ObjectProperty where
  prop T := IsFamily ((Picard.relativeProjection f).app T.as.unop)

instance : (familyProperty f).IsClosedUnderMapObj where
  map_obj {T U M} hM h := by
    change IsFamily ((Picard.relativeProjection f).app U.as.unop)
      ((Scheme.Modules.pullback ((Picard.relativeSpace f).map h.as.unop)).obj M)
    let : M.IsFinitePresentation := hM.1
    exact ⟨Modules.isFinitePresentation_pullback _ M,
      Modules.isFlatOver_pullback_of_isPullback
        (Picard.relativeProjection_isPullback f h.as.unop) M hM.2⟩

instance : (familyProperty f).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms T := by
    change ObjectProperty.IsClosedUnderIsomorphisms
      (IsFamily ((Picard.relativeProjection f).app T.as.unop))
    infer_instance

namespace Family

/-- The full family categories with the inherited ordinary pullback comparisons and coherence. -/
def pseudofunctor : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat :=
  (familyProperty f).fullsubcategory

/-- Ordinary pullback of families along any morphism of test schemes. -/
def pullback {T U : Over S} (h : U ⟶ T) :
    Family ((Picard.relativeProjection f).app T) ⥤
      Family ((Picard.relativeProjection f).app U) :=
  ((pseudofunctor f).map h.op.toLoc).toFunctor

/-- Forgetting the family conditions recovers the ordinary module pullback on objects and maps. -/
def pullbackForgetIso {T U : Over S} (h : U ⟶ T) :
    pullback f h ⋙ forget ((Picard.relativeProjection f).app U) ≅
      forget ((Picard.relativeProjection f).app T) ⋙
        Scheme.Modules.pullback ((Picard.relativeSpace f).map h) :=
  Iso.refl _

/-- The identity comparison inherited from module pullback and the relative-space functor. -/
def pullbackId (T : Over S) :
    pullback f (𝟙 T) ≅ 𝟭 (Family ((Picard.relativeProjection f).app T)) :=
  Cat.Hom.toNatIso ((pseudofunctor f).mapId (.mk (op T)))

/-- The composition comparison inherited from ordinary module pullback. -/
def pullbackComp {T U V : Over S} (h : V ⟶ U) (k : U ⟶ T) :
    pullback f k ⋙ pullback f h ≅ pullback f (h ≫ k) :=
  (Cat.Hom.toNatIso ((pseudofunctor f).mapComp k.op.toLoc h.op.toLoc)).symm

end Family

namespace FamilyGroupoid

/-- The contravariant pseudofunctor of actual flat finitely presented family groupoids. -/
def pseudofunctor : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat :=
  corePseudofunctor (Family.pseudofunctor f)

/-- Ordinary pullback on the actual isomorphism groupoids of families. -/
def pullback {T U : Over S} (h : U ⟶ T) :
    FamilyGroupoid f T ⥤ FamilyGroupoid f U :=
  (Family.pullback f h).core

/-- The underlying module functor is exactly ordinary pullback. -/
def pullbackForgetIso {T U : Over S} (h : U ⟶ T) :
    pullback f h ⋙ forget f U ≅
      forget f T ⋙ Scheme.Modules.pullback ((Picard.relativeSpace f).map h) :=
  Iso.refl _

/-- Identity comparison on actual family groupoids. -/
def pullbackId (T : Over S) :
    pullback f (𝟙 T) ≅ 𝟭 (FamilyGroupoid f T) :=
  (Family.pullbackId f T).core

/-- Composition comparison on actual family groupoids. -/
def pullbackComp {T U V : Over S} (h : V ⟶ U) (k : U ⟶ T) :
    pullback f k ⋙ pullback f h ≅ pullback f (h ≫ k) :=
  (Cat.Hom.toNatIso ((pseudofunctor f).mapComp k.op.toLoc h.op.toLoc)).symm

/-- The pseudofunctor has the actual family groupoid at each test scheme. -/
@[simp]
lemma pseudofunctor_obj (T : Over S) :
    (pseudofunctor f).obj (.mk (op T)) = Cat.of (FamilyGroupoid f T) := rfl

/-- Its restrictions are exactly the ordinary pullback functors. -/
@[simp]
lemma pseudofunctor_map {T U : Over S} (h : U ⟶ T) :
    ((pseudofunctor f).map h.op.toLoc).toFunctor = pullback f h := rfl

/-- Its identity comparison is the displayed ordinary pullback comparison. -/
@[simp]
lemma pseudofunctor_mapId (T : Over S) :
    Cat.Hom.toNatIso ((pseudofunctor f).mapId (.mk (op T))) = pullbackId f T := rfl

/-- Its composition comparison is the displayed ordinary pullback comparison. -/
@[simp]
lemma pseudofunctor_mapComp {T U V : Over S} (h : V ⟶ U) (k : U ⟶ T) :
    Cat.Hom.toNatIso ((pseudofunctor f).mapComp k.op.toLoc h.op.toLoc) =
      (pullbackComp f h k).symm := rfl

/-- The underlying object is its ordinary module pullback. -/
@[simp]
lemma pullback_obj {T U : Over S} (h : U ⟶ T) (M : FamilyGroupoid f T) :
    ((pullback f h).obj M).of.obj =
      (Scheme.Modules.pullback ((Picard.relativeSpace f).map h)).obj M.of.obj := rfl

/-- The action on all actual isomorphisms is ordinary module pullback. -/
@[simp]
lemma pullback_homEquiv {T U : Over S} (h : U ⟶ T)
    {M N : FamilyGroupoid f T} (a : M ⟶ N) :
    homEquiv f U ((pullback f h).map a) =
      (Scheme.Modules.pullback ((Picard.relativeSpace f).map h)).mapIso
        (homEquiv f T a) := by
  apply Iso.ext
  rfl

end FamilyGroupoid

end Langlands.AlgebraicGeometry.CoherentSheaves
