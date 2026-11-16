import Langlands.Geometry.FormalGroup.AtlasReduction
import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlongSquare

/-! # Reduction and change of the actual nilpotent coefficient algebra -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {π : R}
variable {A B : Nilp.{v, w} R π}
variable {σ τ : Type} [Finite σ] [Finite τ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X : BasicAtlas O A.obj σ} {Y : BasicAtlas O A.obj τ}
variable {h : X.opens = Y.opens}

/-- The actual covers from reduction after base change and base change after reduction agree. -/
theorem reductionBaseChangeOpens_eq (X : BasicAtlas O A.obj σ) (f : A ⟶ B) :
    ((X.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)).opens =
      (X.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)).opens :=
  X.baseAlongSquareOpens_eq (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The actual formal atlas comparison for the canonical quotient naturality square. -/
def reductionBaseChangeIso (X : BasicAtlas O A.obj σ) (f : A ⟶ B) :
    Iso ((X.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B))
      (X.reduction.baseChangeAlong (Nilp.reducedScalarMap O f))
      (X.reductionBaseChangeOpens_eq f) :=
  X.baseAlongSquareIso (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The quotient comparison realizes the forward square on complete compatible families. -/
theorem reductionBaseChange_onPoints (X : BasicAtlas O A.obj σ) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj B).obj)
    (x : X.Point (restrictCoefficientAlgebra
      ((Nilp.quotientO O B).comp (Nilp.scalarMap O f)) C)) :
    (X.reductionBaseChangeIso f).onPoints C
      ((X.baseChangeAlong (Nilp.scalarMap O f)).reductionPointEquiv (A := B) C
        (X.baseChangeAlongPointEquiv (Nilp.scalarMap O f)
          (restrictCoefficientAlgebra (Nilp.quotientO O B) C) x)) =
      X.reduction.baseChangeAlongPointEquiv (Nilp.reducedScalarMap O f) C
        (X.reductionPointEquiv (restrictCoefficientAlgebra (Nilp.reducedScalarMap O f) C)
          (X.baseAlongEqPointEquiv (Nilp.quotientO_natural O f) C x)) :=
  X.baseAlongSquare_onPoints (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f) C x

/-- The same actual inverse realizes the reverse complete-family quotient square. -/
theorem reductionBaseChange_inv_onPoints (X : BasicAtlas O A.obj σ) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj B).obj)
    (x : X.Point (restrictCoefficientAlgebra
      ((Nilp.quotientO O B).comp (Nilp.scalarMap O f)) C)) :
    ((X.reductionBaseChangeIso f).onPoints C).symm
      (X.reduction.baseChangeAlongPointEquiv (Nilp.reducedScalarMap O f) C
        (X.reductionPointEquiv (restrictCoefficientAlgebra (Nilp.reducedScalarMap O f) C)
          (X.baseAlongEqPointEquiv (Nilp.quotientO_natural O f) C x))) =
      (X.baseChangeAlong (Nilp.scalarMap O f)).reductionPointEquiv (A := B) C
        (X.baseChangeAlongPointEquiv (Nilp.scalarMap O f)
          (restrictCoefficientAlgebra (Nilp.quotientO O B) C) x) :=
  X.baseAlongSquare_inv_onPoints (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f) C x

namespace Hom

/-- Reduction and varying-Nilp base change commute with every integral formal map. -/
theorem reductionBaseChange_natural (a : Hom X Y h) (f : A ⟶ B) :
    (Y.reductionBaseChangeIso f).hom.comp
        (h := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)) =
      (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)).comp
        (X.reductionBaseChangeIso f).hom :=
  a.baseAlongSquare_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The same inverse gives the reverse integral reduction/base-change square. -/
theorem reductionBaseChange_inv_natural (a : Hom X Y h) (f : A ⟶ B) :
    ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)).comp
        (k := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (X.reductionBaseChangeIso f).inv =
      (Y.reductionBaseChangeIso f).inv.comp
        (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)) :=
  a.baseAlongSquare_inv_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

end Hom

variable {F : Type z} [Field F] [Algebra O F]

namespace RationalHom

/-- The canonical quotient square is natural on the entire global rational Hom. -/
theorem reductionBaseChange_natural (a : RationalHom F X Y h) (f : A ⟶ B) :
    comp (h := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (ofHom (F := F) (Y.reductionBaseChangeIso f).hom)
        (reduction (A := B) (X := X.baseChangeAlong (Nilp.scalarMap O f))
          (Y := Y.baseChangeAlong (Nilp.scalarMap O f))
          (h := baseAlongMapOpens_eq X Y (Nilp.scalarMap O f) h)
          (baseChangeAlong (X := X) (Y := Y) (h := h) (Nilp.scalarMap O f) a)) =
      comp (baseChangeAlong (X := X.reduction) (Y := Y.reduction)
          (h := reductionOpens_eq h) (Nilp.reducedScalarMap O f)
          (reduction (X := X) (Y := Y) (h := h) a))
        (ofHom (X.reductionBaseChangeIso f).hom) :=
  baseAlongSquare_natural a (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The inverse quotient comparison is natural on every global tensor map. -/
theorem reductionBaseChange_inv_natural (a : RationalHom F X Y h) (f : A ⟶ B) :
    comp (k := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (reduction (A := B) (X := X.baseChangeAlong (Nilp.scalarMap O f))
          (Y := Y.baseChangeAlong (Nilp.scalarMap O f))
          (h := baseAlongMapOpens_eq X Y (Nilp.scalarMap O f) h)
          (baseChangeAlong (X := X) (Y := Y) (h := h) (Nilp.scalarMap O f) a))
        (ofHom (F := F) (X.reductionBaseChangeIso f).inv) =
      comp (ofHom (Y.reductionBaseChangeIso f).inv)
        (baseChangeAlong (X := X.reduction) (Y := Y.reduction)
          (h := reductionOpens_eq h) (Nilp.reducedScalarMap O f)
          (reduction (X := X) (Y := Y) (h := h) a)) :=
  baseAlongSquare_inv_natural a (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

end RationalHom

section FractionField

variable [IsDomain O] [IsFractionRing O F]

/-- Rationalize both actual quotient-square formal maps and their inverse equations. -/
def reductionBaseChangeQuasiIsogeny (X : BasicAtlas O A.obj σ) (f : A ⟶ B) :
    QuasiIsogeny F ((X.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B))
      (X.reduction.baseChangeAlong (Nilp.reducedScalarMap O f))
      (X.reductionBaseChangeOpens_eq f) :=
  QuasiIsogeny.ofIso (X.reductionBaseChangeIso f)

@[simp]
theorem reductionBaseChangeQuasiIsogeny_hom (X : BasicAtlas O A.obj σ) (f : A ⟶ B) :
    (X.reductionBaseChangeQuasiIsogeny (F := F) f).hom =
      RationalHom.ofHom (X.reductionBaseChangeIso f).hom := rfl

@[simp]
theorem reductionBaseChangeQuasiIsogeny_inv (X : BasicAtlas O A.obj σ) (f : A ⟶ B) :
    (X.reductionBaseChangeQuasiIsogeny (F := F) f).inv =
      RationalHom.ofHom (X.reductionBaseChangeIso f).inv := rfl

namespace QuasiIsogeny

/-- The quotient comparison commutes with whole actual quasi-isogenies. -/
theorem reductionBaseChange_natural (a : QuasiIsogeny F X Y h) (f : A ⟶ B) :
    ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)).trans
        (h := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        (Y.reductionBaseChangeQuasiIsogeny f) =
      (X.reductionBaseChangeQuasiIsogeny f).trans
        (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)) :=
  a.baseAlongSquare_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The reverse quotient comparison commutes with whole actual quasi-isogenies. -/
theorem reductionBaseChange_inv_natural (a : QuasiIsogeny F X Y h) (f : A ⟶ B) :
    (X.reductionBaseChangeQuasiIsogeny f).symm.trans
        (k := baseAlongCompMapOpens_eq X Y (Nilp.scalarMap O f) (Nilp.quotientO O B) h)
        ((a.baseChangeAlong (Nilp.scalarMap O f)).reduction (A := B)) =
      (a.reduction.baseChangeAlong (Nilp.reducedScalarMap O f)).trans
        (Y.reductionBaseChangeQuasiIsogeny f).symm :=
  a.baseAlongSquare_inv_natural (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

end QuasiIsogeny

end FractionField

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
