import Langlands.Geometry.FormalGroup.AtlasOrderCoefficientUnit
import Langlands.Geometry.FormalGroup.AtlasOrderReductionBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonIdentity

/-! # Actual identity coherence of the Nilp quotient-square comparison -/

noncomputable section

universe u v w z t

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {D : Type t} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section CoefficientIdentity

variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {X : BasicAtlas O R σ}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical coefficient square with identity first map has exactly the actual unit composite. -/
theorem baseAlongSquare_identity_unit (E : OrderAction D X) (f : R →ₐ[O] S)
    {m : S →ₐ[O] S} (hm : m = AlgHom.id O S)
    (e : f.comp (AlgHom.id O R) = m.comp f) :
    (((E.baseAlongSquareIso (AlgHom.id O R) f f m e).trans
      ((E.baseChangeAlong f).baseAlongEqIso hm)).trans (E.baseChangeAlong f).baseIdIso) =
        E.baseIdIso.baseChangeAlong f := by
  cases hm
  have hl := E.baseAlongCompIso_left_unit f
  have hr := E.baseAlongCompIso_right_unit f
  apply Iso.ext_hom
  change (E.baseChangeAlong f).baseIdIso.hom.comp
    ((Hom.id _).comp ((E.baseAlongCompIso f (AlgHom.id O S)).inv.comp
      ((E.baseAlongEqIso e).hom.comp (E.baseAlongCompIso (AlgHom.id O R) f).hom))) =
    (E.baseIdIso.baseChangeAlong f).hom
  rw [hl, hr]
  change (E.baseChangeAlong f).baseIdIso.hom.comp
    ((Hom.id _).comp ((E.baseChangeAlong f).baseIdIso.inv.comp
      ((Hom.id _).comp (E.baseIdIso.baseChangeAlong f).hom))) = _
  let a := (E.baseChangeAlong f).baseIdIso
  let b := (E.baseIdIso.baseChangeAlong f).hom
  have hm := Hom.id_comp (a.inv.comp ((Hom.id _).comp b))
  have hi := Hom.id_comp b
  exact (congrArg (fun z => a.hom.comp z) hm).trans
    ((congrArg (fun z => a.hom.comp (a.inv.comp z)) hi).trans
      ((Hom.comp_assoc a.hom a.inv b).symm.trans
        ((congrArg (fun z => z.comp b) a.hom_inv).trans (Hom.id_comp b))))

end CoefficientIdentity

section NilpIdentity

variable {R : Type v} [CommRing R] [Algebra O R] {r : R}
variable {A : Nilp.{v, w} R r} {X : BasicAtlas O A.obj σ}

/-- The actual identity-coordinate scalar correction forced by the quotient functor's identity law. -/
def reductionIdentityScalarIso (E : OrderAction D X) :=
  E.reduction.baseAlongEqIso
    (congrArg (Nilp.scalarMap O) ((Nilp.reductionFunctor R r).map_id A))

/-- The actual reduced identity-base map is the corrected canonical quotient-square unit route. -/
theorem reductionBaseChange_identity_unit (E : OrderAction D X) :
    (((E.reductionBaseChangeIso (𝟙 A)).trans E.reductionIdentityScalarIso).trans E.reduction.baseIdIso) =
      E.baseIdIso.reduction :=
  E.baseAlongSquare_identity_unit (Nilp.quotientO O A)
    (congrArg (Nilp.scalarMap O) ((Nilp.reductionFunctor R r).map_id A))
    (Nilp.quotientO_natural O (𝟙 A))

variable [IsDomain O] {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]

/-- The four actual rational test maps identifying the corrected quotient-unit and reduced identity routes. -/
def reductionIdentityUnitTestSquare (E : OrderAction D X)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (b : X.reduction.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj A).obj C b.val)) :=
  let a := (((E.reductionBaseChangeIso (𝟙 A)).trans E.reductionIdentityScalarIso).trans
    E.reduction.baseIdIso).onChart C b hb
  let c := E.baseIdIso.reduction.onChart C b hb
  ModuleLaw.OrderAction.Iso.rationalSquare (F := F) a (ModuleLaw.OrderAction.Iso.refl _)
    c (ModuleLaw.OrderAction.Iso.refl _) (by
      have h := congrArg (fun z => z.onChart C b hb) E.reductionBaseChange_identity_unit
      apply ModuleLaw.OrderAction.Iso.ext_hom
      change (ModuleLaw.OrderAction.Hom.id _).comp a.hom = (ModuleLaw.OrderAction.Hom.id _).comp c.hom
      simp only [ModuleLaw.OrderAction.Hom.id_comp]
      exact congrArg ModuleLaw.OrderAction.Iso.hom h)

end NilpIdentity

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
