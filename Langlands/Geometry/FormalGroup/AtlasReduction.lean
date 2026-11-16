import Langlands.Geometry.FormalGroup.ModuleReduction
import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlong

/-! # Reduction of actual formal O-module atlases modulo the distinguished element -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {π : R}
variable {A : Nilp.{v, w} R π}
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X : BasicAtlas O A.obj σ} {Y : BasicAtlas O A.obj τ}
variable {Z : BasicAtlas O A.obj υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend all actual atlas coefficients along the quotient A → A/(π). -/
def reduction (X : BasicAtlas O A.obj σ) :
    BasicAtlas O ((Nilp.reductionFunctor R π).obj A).obj σ :=
  X.baseChangeAlong (Nilp.quotientO O A)

/-- Reduction uses exactly the images of the original principal generators. -/
@[simp]
theorem reduction_opens (X : BasicAtlas O A.obj σ) :
    X.reduction.opens = (Nilp.quotientO O A) '' X.opens := rfl

/-- Equal original covers remain equal under the actual quotient map. -/
theorem reductionOpens_eq (h : X.opens = Y.opens) : X.reduction.opens = Y.reduction.opens :=
  baseOpens_eq (coefficientTest (Nilp.quotientO O A)) h

/-- The complete reduced families are the original families on quotient-algebra tests. -/
def reductionPointEquiv (X : BasicAtlas O A.obj σ)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj) :
    X.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B) ≃ₗ[O]
      X.reduction.Point B :=
  X.baseChangeAlongPointEquiv (Nilp.quotientO O A) B

/-- The entire-family reduction comparison is natural in every further test map. -/
theorem reductionPointEquiv_natural (X : BasicAtlas O A.obj σ)
    {B C : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj} (f : B ⟶ C)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B)) :
    X.reduction.mapPoints f (X.reductionPointEquiv B x) =
      X.reductionPointEquiv C
        (X.mapPoints (restrictCoefficientMap (Nilp.quotientO O A) f) x) :=
  X.baseChangeAlongPointEquiv_natural (Nilp.quotientO O A) f x

/-- Natural comparison of the actual module-valued family functors on reduced tests. -/
def reductionPointFunctorIso (X : BasicAtlas O A.obj σ) :
    restrictCoefficientFunctor (Nilp.quotientO O A) ⋙ X.pointFunctor ≅
      X.reduction.pointFunctor :=
  X.baseChangeAlongPointFunctorIso (Nilp.quotientO O A)

namespace Hom

/-- Reduce actual integral formal atlas maps along the quotient coefficient map. -/
def reduction (q : Hom X Y h) : Hom X.reduction Y.reduction (reductionOpens_eq h) :=
  q.baseChangeAlong (Nilp.quotientO O A)

@[simp]
theorem reduction_id (X : BasicAtlas O A.obj σ) :
    (Hom.id X).reduction = Hom.id X.reduction :=
  baseChangeAlong_id X (Nilp.quotientO O A)

@[simp]
theorem reduction_comp (q : Hom Y Z k) (f : Hom X Y h) :
    (q.comp f).reduction = q.reduction.comp f.reduction :=
  baseChangeAlong_comp q f (Nilp.quotientO O A)

/-- The reduced formal map realizes the whole-family comparison square. -/
theorem reduction_onPoints (q : Hom X Y h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B)) :
    q.reduction.onPoints B (X.reductionPointEquiv B x) =
      Y.reductionPointEquiv B
        (q.onPoints (restrictCoefficientAlgebra (Nilp.quotientO O A) B) x) :=
  q.baseChangeAlong_onPoints (Nilp.quotientO O A) B x

/-- The same formal map also commutes with the inverse whole-family comparisons. -/
theorem reduction_fromPoints (q : Hom X Y h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (y : X.reduction.Point B) :
    q.onPoints (restrictCoefficientAlgebra (Nilp.quotientO O A) B)
        ((X.reductionPointEquiv B).symm y) =
      (Y.reductionPointEquiv B).symm (q.reduction.onPoints B y) :=
  q.baseChangeAlong_fromPoints (Nilp.quotientO O A) B y

end Hom

namespace Iso

/-- Reduce both actual integral formal maps and their two inverse equations. -/
def reduction (q : Iso X Y h) : Iso X.reduction Y.reduction (reductionOpens_eq h) :=
  q.baseChangeAlong (Nilp.quotientO O A)

@[simp]
theorem reduction_hom (q : Iso X Y h) : q.reduction.hom = q.hom.reduction :=
  (q.baseChange (coefficientTest (Nilp.quotientO O A))).reAlgebra_hom _
    (coefficientAlgebraAlong_eq (Nilp.quotientO O A))

@[simp]
theorem reduction_inv (q : Iso X Y h) : q.reduction.inv = q.inv.reduction :=
  (q.baseChange (coefficientTest (Nilp.quotientO O A))).reAlgebra_inv _
    (coefficientAlgebraAlong_eq (Nilp.quotientO O A))

end Iso

namespace RationalHom

variable {F : Type z} [Field F] [Algebra O F]

/-- Reduction is F-linear on global tensor-product formal atlas Hom. -/
def reduction : RationalHom F X Y h →ₗ[F]
    RationalHom F X.reduction Y.reduction (reductionOpens_eq h) :=
  baseChangeAlong (X := X) (Y := Y) (h := h) (Nilp.quotientO O A)

@[simp]
theorem reduction_ofHom (q : Hom X Y h) :
    reduction (ofHom (F := F) q) = ofHom q.reduction :=
  baseChangeAlong_ofHom (Nilp.quotientO O A) q

@[simp]
theorem reduction_id (X : BasicAtlas O A.obj σ) :
    reduction (id (F := F) X) = id X.reduction :=
  baseChangeAlong_id X (Nilp.quotientO O A)

@[simp]
theorem reduction_comp (q : RationalHom F Y Z k) (f : RationalHom F X Y h) :
    reduction (comp q f) = comp (reduction q) (reduction f) :=
  baseChangeAlong_comp q f (Nilp.quotientO O A)

end RationalHom

namespace QuasiIsogeny

variable {F : Type z} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Reduce both actual global rational maps, retaining both inverse equations. -/
def reduction (q : QuasiIsogeny F X Y h) :
    QuasiIsogeny F X.reduction Y.reduction (reductionOpens_eq h) :=
  q.baseChangeAlong (Nilp.quotientO O A)

@[simp]
theorem reduction_hom (q : QuasiIsogeny F X Y h) :
    q.reduction.hom = RationalHom.reduction q.hom := rfl

@[simp]
theorem reduction_inv (q : QuasiIsogeny F X Y h) :
    q.reduction.inv = RationalHom.reduction q.inv := rfl

@[simp]
theorem reduction_refl (X : BasicAtlas O A.obj σ) :
    (refl (F := F) X).reduction = refl X.reduction :=
  baseChangeAlong_refl X (Nilp.quotientO O A)

@[simp]
theorem reduction_symm (q : QuasiIsogeny F X Y h) :
    q.symm.reduction = q.reduction.symm :=
  baseChangeAlong_symm q (Nilp.quotientO O A)

@[simp]
theorem reduction_trans (q : QuasiIsogeny F X Y h) (f : QuasiIsogeny F Y Z k) :
    (q.trans f).reduction = q.reduction.trans f.reduction :=
  baseChangeAlong_trans q f (Nilp.quotientO O A)

@[simp]
theorem reduction_ofIso (q : Iso X Y h) :
    (ofIso (F := F) q).reduction = ofIso q.reduction :=
  baseChangeAlong_ofIso q (Nilp.quotientO O A)

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
