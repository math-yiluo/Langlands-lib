import Langlands.Geometry.FormalGroup.AtlasOrderReduction
import Langlands.Geometry.FormalGroup.AtlasReductionBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongSquare

/-! # Reduction and varying nilpotent coefficients with the full acting order -/

noncomputable section

universe u v w z t

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {π : R}
variable {D : Type t} [Ring D] [Algebra O D]
variable {A B : Nilp.{v, w} R π}
variable {σ τ : Type} [Finite σ] [Finite τ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X : BasicAtlas O A.obj σ} {Y : BasicAtlas O A.obj τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

/-- The actual formal atlas comparison for the canonical quotient naturality square. -/
def reductionBaseChangeIso (E : OrderAction D X) (f : A ⟶ B) :
    Iso ((E.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B))
      (E.reduction.baseChangeAlong (Nilp.reducedScalarMap O f))
      (X.reductionBaseChangeOpens_eq f) :=
  E.baseAlongSquareIso (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- Forgetting the full order retains the actual forward quotient comparison. -/
@[simp]
theorem reductionBaseChangeIso_hom_val (E : OrderAction D X) (f : A ⟶ B) :
    (E.reductionBaseChangeIso f).hom.val = (X.reductionBaseChangeIso f).hom :=
  E.baseAlongSquareIso_hom_val (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- Forgetting the full order retains the actual inverse quotient comparison. -/
@[simp]
theorem reductionBaseChangeIso_inv_val (E : OrderAction D X) (f : A ⟶ B) :
    (E.reductionBaseChangeIso f).inv.val = (X.reductionBaseChangeIso f).inv :=
  E.baseAlongSquareIso_inv_val (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The quotient comparison realizes the forward square on complete compatible families. -/
theorem reductionBaseChange_onPoints (E : OrderAction D X) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj B).obj)
    (x : E.Point (restrictCoefficientAlgebra
      ((Nilp.quotientO O B).comp (Nilp.scalarMap O f)) C)) :
    (E.reductionBaseChangeIso f).onPoints C
      ((E.baseChangeAlong (Nilp.scalarMap O f)).reductionPointEquiv (A := B) C
        (E.baseChangeAlongPointEquiv (Nilp.scalarMap O f)
          (restrictCoefficientAlgebra (Nilp.quotientO O B) C) x)) =
      E.reduction.baseChangeAlongPointEquiv (Nilp.reducedScalarMap O f) C
        (E.reductionPointEquiv (restrictCoefficientAlgebra (Nilp.reducedScalarMap O f) C)
          (E.baseAlongEqPointEquiv (Nilp.quotientO_natural O f) C x)) :=
  E.baseAlongSquare_onPoints (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f) C x

/-- The same actual inverse realizes the reverse complete-family quotient square. -/
theorem reductionBaseChange_inv_onPoints (E : OrderAction D X) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj B).obj)
    (x : E.Point (restrictCoefficientAlgebra
      ((Nilp.quotientO O B).comp (Nilp.scalarMap O f)) C)) :
    ((E.reductionBaseChangeIso f).onPoints C).symm
      (E.reduction.baseChangeAlongPointEquiv (Nilp.reducedScalarMap O f) C
        (E.reductionPointEquiv (restrictCoefficientAlgebra (Nilp.reducedScalarMap O f) C)
          (E.baseAlongEqPointEquiv (Nilp.quotientO_natural O f) C x))) =
      (E.baseChangeAlong (Nilp.scalarMap O f)).reductionPointEquiv (A := B) C
        (E.baseChangeAlongPointEquiv (Nilp.scalarMap O f)
          (restrictCoefficientAlgebra (Nilp.quotientO O B) C) x) :=
  E.baseAlongSquare_inv_onPoints (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f) C x

namespace Hom

/-- Reduction and varying-Nilp base change commute with every integral full-order formal map. -/
theorem reductionBaseChange_natural (a : Hom E E' h) (f : A ⟶ B) :
    (E'.reductionBaseChangeIso f).hom.comp
        (h := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)) =
      (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)).comp
        (E.reductionBaseChangeIso f).hom :=
  a.baseAlongSquare_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The same inverse gives the reverse integral reduction/base-change square. -/
theorem reductionBaseChange_inv_natural (a : Hom E E' h) (f : A ⟶ B) :
    ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)).comp
        (k := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (E.reductionBaseChangeIso f).inv =
      (E'.reductionBaseChangeIso f).inv.comp
        (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)) :=
  a.baseAlongSquare_inv_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

end Hom

variable {F : Type z} [Field F] [Algebra O F]

namespace RationalHom

/-- The canonical quotient square is natural on the entire chartwise rational centralizer. -/
theorem reductionBaseChange_natural (a : RationalHom F E E' h) (f : A ⟶ B) :
    comp (h := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (ofHom (F := F) (E'.reductionBaseChangeIso f).hom)
        (reduction (A := B) (E := E.baseChangeAlong (Nilp.scalarMap O f))
          (E' := E'.baseChangeAlong (Nilp.scalarMap O f))
          (h := baseAlongOpens_eq X Y (Nilp.scalarMap O f) h)
          (baseChangeAlong (E := E) (E' := E') (h := h) (Nilp.scalarMap O f) a)) =
      comp (baseChangeAlong (E := E.reduction) (E' := E'.reduction)
          (h := reductionOpens_eq h) (Nilp.reducedScalarMap O f)
          (reduction (E := E) (E' := E') (h := h) a))
        (ofHom (E.reductionBaseChangeIso f).hom) :=
  baseAlongSquare_natural a (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The inverse quotient comparison is natural on every rational centralizer map. -/
theorem reductionBaseChange_inv_natural (a : RationalHom F E E' h) (f : A ⟶ B) :
    comp (k := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (reduction (A := B) (E := E.baseChangeAlong (Nilp.scalarMap O f))
          (E' := E'.baseChangeAlong (Nilp.scalarMap O f))
          (h := baseAlongOpens_eq X Y (Nilp.scalarMap O f) h)
          (baseChangeAlong (E := E) (E' := E') (h := h) (Nilp.scalarMap O f) a))
        (ofHom (F := F) (E.reductionBaseChangeIso f).inv) =
      comp (ofHom (E'.reductionBaseChangeIso f).inv)
        (baseChangeAlong (E := E.reduction) (E' := E'.reduction)
          (h := reductionOpens_eq h) (Nilp.reducedScalarMap O f)
          (reduction (E := E) (E' := E') (h := h) a)) :=
  baseAlongSquare_inv_natural a (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both actual quotient-square formal maps and their inverse equations. -/
def reductionBaseChangeQuasiIsogeny (E : OrderAction D X) (f : A ⟶ B) :
    QuasiIsogeny F ((E.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B))
      (E.reduction.baseChangeAlong (Nilp.reducedScalarMap O f))
      (X.reductionBaseChangeOpens_eq f) :=
  QuasiIsogeny.ofIso (E.reductionBaseChangeIso f)

@[simp]
theorem reductionBaseChangeQuasiIsogeny_hom (E : OrderAction D X) (f : A ⟶ B) :
    (E.reductionBaseChangeQuasiIsogeny (F := F) f).hom =
      RationalHom.ofHom (E.reductionBaseChangeIso f).hom := rfl

@[simp]
theorem reductionBaseChangeQuasiIsogeny_inv (E : OrderAction D X) (f : A ⟶ B) :
    (E.reductionBaseChangeQuasiIsogeny (F := F) f).inv =
      RationalHom.ofHom (E.reductionBaseChangeIso f).inv := rfl

/-- Forgetting the full order retains the entire ambient quotient quasi-isogeny. -/
@[simp]
theorem reductionBaseChangeQuasiIsogeny_toAtlas (E : OrderAction D X) (f : A ⟶ B) :
    (E.reductionBaseChangeQuasiIsogeny (F := F) f).toAtlasQuasiIsogeny =
      X.reductionBaseChangeQuasiIsogeny f :=
  E.baseAlongSquareQuasiIsogeny_toAtlas (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

namespace QuasiIsogeny

/-- The quotient comparison commutes with whole actual quasi-isogenies. -/
theorem reductionBaseChange_natural (a : QuasiIsogeny F E E' h) (f : A ⟶ B) :
    ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)).trans
        (h := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (E'.reductionBaseChangeQuasiIsogeny f) =
      (E.reductionBaseChangeQuasiIsogeny f).trans
        (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)) :=
  a.baseAlongSquare_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The reverse quotient comparison commutes with whole actual quasi-isogenies. -/
theorem reductionBaseChange_inv_natural (a : QuasiIsogeny F E E' h) (f : A ⟶ B) :
    (E.reductionBaseChangeQuasiIsogeny f).symm.trans
        (k := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)) =
      (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)).trans
        (E'.reductionBaseChangeQuasiIsogeny f).symm :=
  a.baseAlongSquare_inv_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
