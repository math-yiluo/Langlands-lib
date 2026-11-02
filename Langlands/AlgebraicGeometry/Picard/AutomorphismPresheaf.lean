import Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismUnits
import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.AlgebraicGeometry.Units.RelativeGlobalUnits
import Langlands.GroupScheme.Multiplicative
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-! # The actual automorphism presheaf of a line bundle -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

private def isoOfPointwiseEquiv {C : Type*} [Category C]
    {F G : C ⥤ Type u} (e : ∀ T, F.obj T ≃ G.obj T)
    (h : ∀ {T U} (f : T ⟶ U) (r : F.obj T),
      e U (F.map f r) = G.map f (e T r)) : F ≅ G :=
  NatIso.ofComponents (fun T => (e T).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro r
    exact h f r)

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {X Y Z : Scheme.{u}}

/-- Units as actual endomorphisms in the line-bundle core. -/
def unitHomEquiv (L : LineBundle X) : Γ(X, ⊤)ˣ ≃ (Core.mk L ⟶ Core.mk L) :=
  (LineBundle.unitAutEquiv L).toEquiv.trans
    { toFun := fun e => ⟨e⟩
      invFun := fun e => e.iso
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

set_option backward.isDefEq.respectTransparency false in
lemma pullHom_unitHomEquiv (L : LineBundle X) (f : Y ⟶ X) (g : Z ⟶ Y)
    (p : Z ⟶ X) (h : g ≫ f = p) (r : Γ(Y, ⊤)ˣ) :
    pullHom (F := pseudofunctor) (unitHomEquiv ((LineBundle.pullback f).obj L) r)
      g p p h h =
    unitHomEquiv ((LineBundle.pullback p).obj L)
      (Units.map g.appTop.hom.toMonoidHom r) := by
  subst p
  simp only [pullHom]
  apply Core.hom_ext
  change (LineBundle.pullbackComp g f).inv.app L ≫
      ((LineBundle.pullback g).mapIso
        (LineBundle.unitAut ((LineBundle.pullback f).obj L) r)).hom ≫
      (LineBundle.pullbackComp g f).hom.app L = _
  rw [LineBundle.pullback_mapIso_unitAut]
  exact congrArg Iso.hom
    (LineBundle.unitAutEquiv_conjugate ((LineBundle.pullbackComp g f).app L)
      (Units.map g.appTop.hom.toMonoidHom r))

set_option backward.isDefEq.respectTransparency false in
/-- The component equivalence, with the automorphism-presheaf target explicit. -/
def automorphismEquivAt (L : LineBundle X) (T : Over X) :
    Γ(T.left, ⊤)ˣ ≃ (pseudofunctor.presheafHom (Core.mk L) (Core.mk L)).obj (op T) :=
  unitHomEquiv ((LineBundle.pullback T.hom).obj L)

set_option backward.isDefEq.respectTransparency false in
lemma automorphismEquivAt_naturality (L : LineBundle X) {T U : Over X}
    (h : T ⟶ U) (r : Γ(U.left, ⊤)ˣ) :
    automorphismEquivAt L T (Units.map h.left.appTop.hom.toMonoidHom r) =
      (pseudofunctor.presheafHom (Core.mk L) (Core.mk L)).map h.op
        (automorphismEquivAt L U r) :=
  (pullHom_unitHomEquiv L U.hom h.left T.hom (Over.w h) r).symm

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary global units identify naturally with the actual automorphism
presheaf, with the full pseudofunctor restriction maps. -/
def unitsAutomorphismPresheafIso (L : LineBundle X) :
    (Langlands.GroupScheme.Gm.unitsFunctor X ⋙ forget CommGrpCat) ≅
      pseudofunctor.presheafHom (Core.mk L) (Core.mk L) :=
  isoOfPointwiseEquiv
    (F := Langlands.GroupScheme.Gm.unitsFunctor X ⋙ forget CommGrpCat)
    (G := pseudofunctor.presheafHom (Core.mk L) (Core.mk L))
    (fun T => automorphismEquivAt L T.unop)
    (by
      intro T U h r
      exact automorphismEquivAt_naturality L h.unop r)

/-- The actual automorphisms of the pullbacks of `L` on all relative test schemes,
in the lifted universe used for algebraic spaces. -/
def relativeAutomorphismPresheaf {S : Scheme.{u}} (f : X ⟶ S)
    (L : LineBundle X) : AlgebraicSpace.Presheaf S :=
  ((Over.pullback f).op ⋙ pseudofunctor.presheafHom (Core.mk L) (Core.mk L)) ⋙
    uliftFunctor.{u + 1}

set_option backward.isDefEq.respectTransparency false in
/-- Global units on actual relative schemes are the actual automorphisms of
the same pulled-back bundle, naturally on every scheme over the base. -/
def relativeUnitsAutomorphismPresheafIso {S : Scheme.{u}} (f : X ⟶ S)
    (L : LineBundle X) :
    RelativeGlobalUnits.presheaf f ≅ relativeAutomorphismPresheaf f L :=
  (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T U h
    rfl)) ≪≫
    isoWhiskerRight (isoWhiskerLeft (Over.pullback f).op
      (unitsAutomorphismPresheafIso L)) uliftFunctor.{u + 1}

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
