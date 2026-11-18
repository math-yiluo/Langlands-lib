import Langlands.Geometry.FormalGroup.AtlasCoefficientSquareComposition
import Langlands.Geometry.FormalGroup.AtlasOrderReductionBaseChange

/-! # Actual composition coherence of the Nilp quotient-square maps -/

noncomputable section

universe u v w t

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {D : Type t} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section CoefficientEquality

variable {R S S' T : Type v} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O S'] [Algebra O T]
variable {X : BasicAtlas O R σ}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Retain the specified coefficient square while changing its last coefficient map by equality. -/
theorem baseAlongSquareIso_target_eq (E : OrderAction D X)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (p : R →ₐ[O] S')
    {q q' : S' →ₐ[O] T} (h : q = q')
    (e : g.comp f = q.comp p) (e' : g.comp f = q'.comp p) :
    (E.baseAlongSquareIso f g p q e).trans ((E.baseChangeAlong p).baseAlongEqIso h) =
      E.baseAlongSquareIso f g p q' e' := by
  cases h
  exact Iso.trans_refl _

end CoefficientEquality

variable {R : Type v} [CommRing R] [Algebra O R] {r : R}
variable {A B C : Nilp.{v,w} R r} {X : BasicAtlas O A.obj σ}

/-- The actual quotient coefficient-composition map, corrected by the quotient functor's composition law. -/
def reductionCompositionScalarIso (E : OrderAction D X) (f : A ⟶ B) (g : B ⟶ C) :=
  (E.reduction.baseAlongCompIso (Nilp.reducedScalarMap O f) (Nilp.reducedScalarMap O g)).trans
    (E.reduction.baseAlongEqIso
      (congrArg (Nilp.scalarMap O) ((Nilp.reductionFunctor R r).map_comp f g)).symm)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual two quotient-square maps compose to the quotient square of the composite Nilp map. -/
theorem reductionBaseChange_comp (E : OrderAction D X) (f : A ⟶ B) (g : B ⟶ C) :
    (((E.baseChangeAlong (Nilp.scalarMap O f)).reductionBaseChangeIso g).trans
      ((E.reductionBaseChangeIso f).baseChangeAlong (Nilp.reducedScalarMap O g))).trans
        (E.reductionCompositionScalarIso f g) =
      ((E.baseAlongCompIso (Nilp.scalarMap O f) (Nilp.scalarMap O g)).reduction).trans
        (E.reductionBaseChangeIso (f ≫ g)) := by
  let hf := Nilp.quotientO_natural O f
  let hg := Nilp.quotientO_natural O g
  let hc := congrArg (Nilp.scalarMap O) ((Nilp.reductionFunctor R r).map_comp f g)
  let ec := (Nilp.quotientO_natural O (f ≫ g)).trans
    (congrArg (fun j => j.comp (Nilp.quotientO O A)) hc)
  let a := (E.baseChangeAlong (Nilp.scalarMap O f)).reductionBaseChangeIso g
  let b := (E.reductionBaseChangeIso f).baseChangeAlong (Nilp.reducedScalarMap O g)
  let c := E.reduction.baseAlongCompIso (Nilp.reducedScalarMap O f) (Nilp.reducedScalarMap O g)
  let ie := E.reduction.baseAlongEqIso hc.symm
  let nc := (E.baseAlongCompIso (Nilp.scalarMap O f) (Nilp.scalarMap O g)).reduction
  let sc := E.baseAlongSquareIso (Nilp.scalarMap O (f ≫ g)) (Nilp.quotientO O C)
    (Nilp.quotientO O A) ((Nilp.reducedScalarMap O g).comp (Nilp.reducedScalarMap O f)) ec
  have he : (a.trans b).trans c = nc.trans sc :=
    E.baseAlongSquareIso_comp (Nilp.scalarMap O f) (Nilp.scalarMap O g)
      (Nilp.quotientO O A) (Nilp.quotientO O B) (Nilp.quotientO O C)
      (Nilp.reducedScalarMap O f) (Nilp.reducedScalarMap O g) hf hg ec
  have hs : sc.trans ie = E.reductionBaseChangeIso (f ≫ g) :=
    E.baseAlongSquareIso_target_eq (Nilp.scalarMap O (f ≫ g)) (Nilp.quotientO O C)
      (Nilp.quotientO O A) hc.symm ec (Nilp.quotientO_natural O (f ≫ g))
  change (a.trans b).trans (c.trans ie) = nc.trans (E.reductionBaseChangeIso (f ≫ g))
  exact (Iso.trans_assoc (a.trans b) c ie).symm.trans
    ((congrArg (fun j => j.trans ie) he).trans
      ((Iso.trans_assoc nc sc ie).trans (congrArg (fun j => nc.trans j) hs)))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
