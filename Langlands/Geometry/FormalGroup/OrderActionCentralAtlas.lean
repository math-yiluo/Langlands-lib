import Langlands.Geometry.FormalGroup.AtlasOrderAction
import Langlands.Geometry.FormalGroup.OrderActionCentralScalars
import Langlands.Geometry.FormalGroup.OrderIso

/-! # Central scalars on a formal atlas with an order action -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {C : Type c} [CommRing C]
variable {R : Type v} [CommRing R] [Algebra O R] [Algebra C R]
variable {D : Type w} [Ring D] [Algebra O D] [Algebra C D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}
variable (E : BasicAtlas.OrderAction D X)
variable (h : ∀ (b : X.opens) (a : C) (x : σ → Localization.Away b.val),
  (E.chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)

/-- The same chart comparison is linear for the central scalar ring. -/
def centralTransition (A : CommAlgCat.{v} R) (b c : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) (hc : IsUnit (algebraMap R A c.val)) :
    ModuleLaw.Iso
      (((E.chart b).centralModule (h b)).map (coefficientLift (O := C) b.val A hb))
      (((E.chart c).centralModule (h c)).map (coefficientLift (O := C) c.val A hc)) := by
  let M := (X.chart b).map (coefficientLift (O := O) b.val A hb)
  let N := (X.chart c).map (coefficientLift (O := O) c.val A hc)
  let t : ModuleLaw.Iso M N := X.transition A b c hb hc
  let f := ModuleLaw.OrderAction.Iso.ofModuleIso t (E.transition A b c hb hc)
  refine {
    hom := ⟨t.hom.toHom, fun a => congrArg (fun g : ModuleLaw.Hom M N => g.toHom)
      (f.hom.commutes (algebraMap C D a))⟩
    inv := ⟨t.inv.toHom, fun a => congrArg (fun g : ModuleLaw.Hom N M => g.toHom)
      (f.inv.commutes (algebraMap C D a))⟩
    inv_hom := ModuleLaw.Hom.ext (congrArg (fun g : ModuleLaw.Hom M M => g.toHom) t.inv_hom)
    hom_inv := ModuleLaw.Hom.ext (congrArg (fun g : ModuleLaw.Hom N N => g.toHom) t.hom_inv) }

/-- Put the central formal module law on each chart, keeping the transition coordinates. -/
def centralAtlas : BasicAtlas C R σ where
  opens := X.opens
  covers := X.covers
  chart b := (E.chart b).centralModule (h b)
  transition := E.centralTransition h
  transition_self A b hb := by
    apply ModuleLaw.Iso.ext_hom
    apply ModuleLaw.Hom.ext
    exact congrArg (fun f => f.hom.toHom) (X.transition_self A b hb)
  transition_cocycle A b c d hb hc hd := by
    apply ModuleLaw.Iso.ext_hom
    apply ModuleLaw.Hom.ext
    exact congrArg (fun f => f.hom.toHom) (X.transition_cocycle A b c d hb hc hd)
  transition_natural φ b c hb hc hb' hc' := X.transition_natural φ b c hb hc hb' hc'

/-- The new scalar ring keeps the order action on the same chart coordinates. -/
def centralAtlasOrder : BasicAtlas.OrderAction D (E.centralAtlas h) where
  chart b := (E.chart b).centralOrder (h b)
  transition A b c hb hc a := by
    apply ModuleLaw.Hom.ext
    let M := (X.chart b).map (coefficientLift (O := O) b.val A hb)
    let N := (X.chart c).map (coefficientLift (O := O) c.val A hc)
    exact congrArg (fun f : ModuleLaw.Hom M N => f.toHom) (E.transition A b c hb hc a)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
