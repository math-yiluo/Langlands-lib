import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Transporting an absolute presheaf representative to its original base -/

universe u

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseTransport

abbrev AbsolutePresheaf := Scheme.{u}ᵒᵖ ⥤ Type (u + 1)

variable {S : Scheme.{u}}

/-- The presheaf of sections lying over the given structure map of a test scheme. -/
def fiberPresheaf {F : AbsolutePresheaf.{u}}
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) : Presheaf S where
  obj U := {x : F.obj (op U.unop.left) //
    s.app (op U.unop.left) x = ULift.up U.unop.hom}
  map {U V} f := TypeCat.ofHom fun x => ⟨F.map f.unop.left.op x.val, by
    rw [s.naturality_apply]
    change ULift.up (f.unop.left ≫ (s.app (op U.unop.left) x.val).down) =
      ULift.up V.unop.hom
    rw [x.property]
    exact congrArg ULift.up f.unop.w⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact F.map_id_apply _ _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    simpa using F.map_comp_apply f.unop.left.op g.unop.left.op x.val

/-- A natural transformation to the base determines the original structure map. -/
def structureMap {F : AbsolutePresheaf.{u}} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ F)
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) : P ⟶ S :=
  (CategoryTheory.uliftYoneda.{u + 1}).preimage (e.hom ≫ s)

@[reassoc (attr := simp)]
lemma structureMap_yoneda {F : AbsolutePresheaf.{u}} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ F)
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) :
    CategoryTheory.uliftYoneda.{u + 1}.map (structureMap e s) = e.hom ≫ s :=
  Functor.map_preimage _ _

/-- The absolute representative, equipped with its induced original structure map. -/
def representativeOver {F : AbsolutePresheaf.{u}} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ F)
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) : Over S :=
  Over.mk (structureMap e s)

/-- The comparison from relative points of the induced representative to the fibre presheaf. -/
def toFiber {F : AbsolutePresheaf.{u}} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ F)
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) :
    (schemeYoneda S).obj (representativeOver e s) ⟶ fiberPresheaf s where
  app U := TypeCat.ofHom fun f => ⟨e.hom.app (op U.unop.left) ⟨f.down.left⟩, by
    have h := congrArg (fun a => a.app (op U.unop.left) ⟨f.down.left⟩)
      (structureMap_yoneda e s)
    exact h.symm.trans (congrArg ULift.up f.down.w)⟩
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact e.hom.naturality_apply f.unop.left.op ⟨x.down.left⟩

lemma toFiber_bijective {F : AbsolutePresheaf.{u}} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ F)
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) (U : Over S) :
    Function.Bijective ((toFiber e s).app (op U)) := by
  constructor
  · intro a b hab
    have h := (ConcreteCategory.bijective_of_isIso (e.hom.app (op U.left))).injective
      (congrArg Subtype.val hab)
    apply ULift.ext
    apply Over.OverMorphism.ext
    exact congrArg ULift.down h
  · intro x
    let f : U.left ⟶ P := (e.inv.app (op U.left) x.val).down
    have hf : f ≫ structureMap e s = U.hom := by
      apply ULift.up_injective
      have h := congrArg (fun a => a.app (op U.left) ⟨f⟩)
        (structureMap_yoneda e s)
      exact h.trans (by
        change s.app (op U.left) (e.hom.app (op U.left)
          (e.inv.app (op U.left) x.val)) = ULift.up U.hom
        rw [e.inv_hom_id_app_apply]
        exact x.property)
    refine ⟨⟨Over.homMk f hf⟩, ?_⟩
    apply Subtype.ext
    exact e.inv_hom_id_app_apply _ x.val

/-- An absolute representative represents the fibre presheaf on all tests over the base. -/
def fiberIso {F : AbsolutePresheaf.{u}} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ F)
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) :
    (schemeYoneda S).obj (representativeOver e s) ≅ fiberPresheaf s := by
  letI : IsIso (toFiber e s) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    exact toFiber_bijective e s U.unop
  exact asIso (toFiber e s)

private lemma eqToHom_apply_heq {A B : Type (u + 1)} (h : A = B) (x : A) :
    (eqToHom h) x ≍ x := by
  cases h
  rfl

/-- The absolute presheaf obtained by retaining all structure maps to the base. -/
def totalPresheaf (F : Presheaf S) : AbsolutePresheaf.{u} where
  obj X := Σ t : X.unop ⟶ S, F.obj (op (Over.mk t))
  map {X Y} f := TypeCat.ofHom fun x =>
    ⟨f.unop ≫ x.1, F.map (Over.homMk f.unop rfl).op x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, x⟩
    apply Sigma.ext (Category.id_comp t)
    have hh : (Over.homMk (𝟙 X.unop) rfl :
        Over.mk (𝟙 X.unop ≫ t) ⟶ Over.mk t) =
        eqToHom (by rw [Category.id_comp]) := by
      ext
      simp
    dsimp
    rw [hh]
    simp only [eqToHom_op, eqToHom_map]
    exact eqToHom_apply_heq _ x
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, x⟩
    apply Sigma.ext (Category.assoc g.unop f.unop t)
    have hh : (Over.homMk (g.unop ≫ f.unop) rfl :
        Over.mk ((g.unop ≫ f.unop) ≫ t) ⟶ Over.mk t) =
        eqToHom (by rw [Category.assoc]) ≫
          (Over.homMk g.unop rfl : Over.mk (g.unop ≫ (f.unop ≫ t)) ⟶
            Over.mk (f.unop ≫ t)) ≫
          (Over.homMk f.unop rfl : Over.mk (f.unop ≫ t) ⟶ Over.mk t) := by
      ext
      simp
    dsimp
    rw [hh]
    simp only [op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
    exact eqToHom_apply_heq _ _

/-- The structure-map projection of the total presheaf. -/
def totalToBase (F : Presheaf S) :
    totalPresheaf F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S where
  app X := TypeCat.ofHom fun x => ⟨x.1⟩
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- A relative section is a total section with its specified original structure map. -/
def toTotalFiber (F : Presheaf S) : F ⟶ fiberPresheaf (totalToBase F) where
  app U := TypeCat.ofHom fun x => ⟨⟨U.unop.hom, x⟩, rfl⟩
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    symm
    apply Sigma.ext f.unop.w
    have hh : (Over.homMk f.unop.left rfl :
        Over.mk (f.unop.left ≫ U.unop.hom) ⟶ U.unop) =
        eqToHom (by
          rw [f.unop.w]
          exact (CostructuredArrow.eq_mk V.unop).symm) ≫ f.unop := by
      ext
      simp
    change F.map (Over.homMk f.unop.left rfl :
      Over.mk (f.unop.left ≫ U.unop.hom) ⟶ U.unop).op x ≍ F.map f x
    rw [hh]
    simp only [op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
    exact eqToHom_apply_heq _ _

lemma toTotalFiber_bijective (F : Presheaf S) (U : Over S) :
    Function.Bijective ((toTotalFiber F).app (op U)) := by
  constructor
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
  · rintro ⟨⟨t, x⟩, ht⟩
    have ht' : t = U.hom := congrArg ULift.down ht
    subst t
    exact ⟨x, rfl⟩

/-- Taking the fibre of the total presheaf recovers the entire relative presheaf. -/
def totalFiberIso (F : Presheaf S) : F ≅ fiberPresheaf (totalToBase F) := by
  letI : IsIso (toTotalFiber F) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    exact toTotalFiber_bijective F U.unop
  exact asIso (toTotalFiber F)

/-- An absolute representative of the total presheaf represents the original relative presheaf. -/
def representationOver {F : Presheaf S} {P : Scheme.{u}}
    (e : CategoryTheory.uliftYoneda.{u + 1}.obj P ≅ totalPresheaf F) :
    (schemeYoneda S).obj (representativeOver e (totalToBase F)) ≅ F :=
  fiberIso e (totalToBase F) ≪≫ (totalFiberIso F).symm

end Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseTransport
