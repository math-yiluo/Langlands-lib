import Langlands.Geometry.FormalGroup.OrderIso
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism

/-! # Actual full-order transition isomorphisms and rational transition squares -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The supplied formal transition commutes with the full order in both directions. -/
def transitionIso (E : OrderAction D X) (B : CommAlgCat.{v} R) (a b : X.opens)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.Iso
      ((E.chart a).map (coefficientLift (O := O) a.val B ha))
      ((E.chart b).map (coefficientLift (O := O) b.val B hb)) :=
  ModuleLaw.OrderAction.Iso.ofModuleIso (X.transition B a b ha hb) (E.transition B a b ha hb)

@[simp]
theorem transitionIso_toModuleIso (E : OrderAction D X) (B : CommAlgCat.{v} R)
    (a b : X.opens) (ha : IsUnit (algebraMap R B a.val))
    (hb : IsUnit (algebraMap R B b.val)) :
    (E.transitionIso B a b ha hb).toModuleIso = X.transition B a b ha hb := rfl

/-- The same-chart order transition is the actual formal identity. -/
theorem transitionIso_self (E : OrderAction D X) (B : CommAlgCat.{v} R)
    (a : X.opens) (ha : IsUnit (algebraMap R B a.val)) :
    E.transitionIso B a a ha ha = ModuleLaw.OrderAction.Iso.refl _ := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  exact congrArg ModuleLaw.Iso.hom (X.transition_self B a ha)

/-- The actual full-order transitions inherit the original formal cocycle. -/
theorem transitionIso_cocycle (E : OrderAction D X) (B : CommAlgCat.{v} R)
    (a b c : X.opens) (ha : IsUnit (algebraMap R B a.val))
    (hb : IsUnit (algebraMap R B b.val)) (hc : IsUnit (algebraMap R B c.val)) :
    (E.transitionIso B a b ha hb).trans (E.transitionIso B b c hb hc) =
      E.transitionIso B a c ha hc := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  exact congrArg ModuleLaw.Iso.hom (X.transition_cocycle B a b c ha hb hc)

variable {F : Type z} [Field F] [Algebra O F]

namespace RationalHom

/-- The rational transition square is an equality in the full-order tensor centralizer. -/
theorem onChart_transition (f : RationalHom F E E' h) (B : CommAlgCat.{v} R)
    (b c : Y.opens) (hb : IsUnit (algebraMap R B b.val))
    (hc : IsUnit (algebraMap R B c.val)) :
    (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
      (E'.transitionIso B b c hb hc).hom).comp (f.onChart B b hb) =
    (f.onChart B c hc).comp
      (ModuleLaw.OrderAction.RationalHom.ofHom
        (E.transitionIso B
          (sourceChart (X := X) (Y := Y) h b)
          (sourceChart (X := X) (Y := Y) h c) hb hc).hom) := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact BasicAtlas.RationalHom.onChart_transition f.val B b c hb hc

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Chart evaluation of an actual quasi-isogeny commutes with both actual order transitions. -/
theorem onChart_transition (f : QuasiIsogeny F E E' h) (B : CommAlgCat.{v} R)
    (b c : Y.opens) (hb : IsUnit (algebraMap R B b.val))
    (hc : IsUnit (algebraMap R B c.val)) :
    (f.onChart B b hb).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (E'.transitionIso B b c hb hc)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        (E.transitionIso B
          (sourceChart (X := X) (Y := Y) h b)
          (sourceChart (X := X) (Y := Y) h c) hb hc)).trans
        (f.onChart B c hc) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact RationalHom.onChart_transition f.hom B b c hb hc

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
