import Langlands.Geometry.FormalGroup.AtlasReduction
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlong

/-! # Reduction of actual formal atlases with their full order actions -/

noncomputable section

universe u v w z t

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {π : R}
variable {D : Type t} [Ring D] [Algebra O D]
variable {A : Nilp.{v, w} R π}
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X : BasicAtlas O A.obj σ} {Y : BasicAtlas O A.obj τ}
variable {Z : BasicAtlas O A.obj υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Extend every actual order-action coefficient along A → A/(π). -/
def reduction (E : OrderAction D X) : OrderAction D X.reduction :=
  E.baseChangeAlong (Nilp.quotientO O A)

/-- The reduced full-order families are the original families on quotient-algebra tests. -/
def reductionPointEquiv (E : OrderAction D X)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj) :
    E.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B) ≃ₗ[D]
      E.reduction.Point B :=
  E.baseChangeAlongPointEquiv (Nilp.quotientO O A) B

/-- Forgetting the order gives precisely the ambient quotient family comparison. -/
theorem reductionPointEquiv_eq (E : OrderAction D X)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (x : E.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B)) :
    E.reductionPointEquiv B x = X.reductionPointEquiv B x :=
  E.baseChangeAlongPointEquiv_eq (Nilp.quotientO O A) B x

/-- Full-order reduction of complete families is natural in every further test map. -/
theorem reductionPointEquiv_natural (E : OrderAction D X)
    {B C : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj} (f : B ⟶ C)
    (x : E.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B)) :
    E.reduction.mapPoints f (E.reductionPointEquiv B x) =
      E.reductionPointEquiv C
        (E.mapPoints (restrictCoefficientMap (Nilp.quotientO O A) f) x) :=
  E.baseChangeAlongPointEquiv_natural (Nilp.quotientO O A) f x

/-- Natural comparison of the actual order-module family functors on reduced tests. -/
def reductionPointFunctorIso (E : OrderAction D X) :
    restrictCoefficientFunctor (Nilp.quotientO O A) ⋙ E.pointFunctor ≅
      E.reduction.pointFunctor :=
  E.baseChangeAlongPointFunctorIso (Nilp.quotientO O A)

namespace Hom

/-- Reduce the actual formal map with its commutation for every order element. -/
def reduction (q : Hom E E' h) :
    Hom E.reduction E'.reduction (reductionOpens_eq h) :=
  q.baseChangeAlong (Nilp.quotientO O A)

/-- Forgetting order commutation retains the actual ambient reduced formal map. -/
@[simp]
theorem reduction_val (q : Hom E E' h) : q.reduction.val = q.val.reduction :=
  q.baseChangeAlong_val (Nilp.quotientO O A)

@[simp]
theorem reduction_id (E : OrderAction D X) :
    (Hom.id E).reduction = Hom.id E.reduction :=
  baseChangeAlong_id E (Nilp.quotientO O A)

@[simp]
theorem reduction_comp (q : Hom E' E'' k) (f : Hom E E' h) :
    (q.comp f).reduction = q.reduction.comp f.reduction :=
  baseChangeAlong_comp q f (Nilp.quotientO O A)

/-- The reduced order-linear formal map realizes the entire-family square. -/
theorem reduction_onPoints (q : Hom E E' h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (x : E.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B)) :
    q.reduction.onPoints B (E.reductionPointEquiv B x) =
      E'.reductionPointEquiv B
        (q.onPoints (restrictCoefficientAlgebra (Nilp.quotientO O A) B) x) :=
  q.baseChangeAlong_onPoints (Nilp.quotientO O A) B x

/-- The same formal map commutes with the inverse whole-family comparisons. -/
theorem reduction_fromPoints (q : Hom E E' h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (y : E.reduction.Point B) :
    q.onPoints (restrictCoefficientAlgebra (Nilp.quotientO O A) B)
        ((E.reductionPointEquiv B).symm y) =
      (E'.reductionPointEquiv B).symm (q.reduction.onPoints B y) :=
  q.baseChangeAlong_fromPoints (Nilp.quotientO O A) B y

end Hom

namespace Iso

/-- Reduce both actual order-linear formal maps and both inverse equations. -/
def reduction (q : Iso E E' h) :
    Iso E.reduction E'.reduction (reductionOpens_eq h) :=
  q.baseChangeAlong (Nilp.quotientO O A)

@[simp]
theorem reduction_hom (q : Iso E E' h) : q.reduction.hom = q.hom.reduction :=
  q.baseChangeAlong_hom (Nilp.quotientO O A)

@[simp]
theorem reduction_inv (q : Iso E E' h) : q.reduction.inv = q.inv.reduction :=
  q.baseChangeAlong_inv (Nilp.quotientO O A)

/-- The reduced order-linear isomorphism realizes the entire-family square. -/
theorem reduction_onPoints (q : Iso E E' h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (x : E.Point (restrictCoefficientAlgebra (Nilp.quotientO O A) B)) :
    q.reduction.onPoints B (E.reductionPointEquiv B x) =
      E'.reductionPointEquiv B
        (q.onPoints (restrictCoefficientAlgebra (Nilp.quotientO O A) B) x) :=
  q.baseChangeAlong_onPoints (Nilp.quotientO O A) B x

/-- The inverse comparisons realize the reverse isomorphism square. -/
theorem reduction_fromPoints (q : Iso E E' h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R π).obj A).obj)
    (y : E.reduction.Point B) :
    q.onPoints (restrictCoefficientAlgebra (Nilp.quotientO O A) B)
        ((E.reductionPointEquiv B).symm y) =
      (E'.reductionPointEquiv B).symm (q.reduction.onPoints B y) :=
  q.baseChangeAlong_fromPoints (Nilp.quotientO O A) B y

end Iso

namespace RationalHom

variable {F : Type z} [Field F] [Algebra O F]

/-- Reduce the entire chartwise rational centralizer, F-linearly. -/
def reduction : RationalHom F E E' h →ₗ[F]
    RationalHom F E.reduction E'.reduction (reductionOpens_eq h) :=
  baseChangeAlong (E := E) (E' := E') (h := h) (Nilp.quotientO O A)

/-- Forgetting commutation retains exactly the ambient global tensor reduction. -/
@[simp]
theorem reduction_val (q : RationalHom F E E' h) :
    (reduction q).val = BasicAtlas.RationalHom.reduction q.val :=
  baseChangeAlong_val (Nilp.quotientO O A) q

@[simp]
theorem reduction_ofHom (q : Hom E E' h) :
    reduction (ofHom (F := F) q) = ofHom q.reduction :=
  baseChangeAlong_ofHom (Nilp.quotientO O A) q

@[simp]
theorem reduction_id (E : OrderAction D X) :
    reduction (id (F := F) E) = id E.reduction :=
  baseChangeAlong_id E (Nilp.quotientO O A)

@[simp]
theorem reduction_comp (q : RationalHom F E' E'' k) (f : RationalHom F E E' h) :
    reduction (comp q f) = comp (reduction q) (reduction f) :=
  baseChangeAlong_comp q f (Nilp.quotientO O A)

end RationalHom

namespace QuasiIsogeny

variable {F : Type z} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Reduce both full-order rational maps and retain both inverse equations. -/
def reduction (q : QuasiIsogeny F E E' h) :
    QuasiIsogeny F E.reduction E'.reduction (reductionOpens_eq h) :=
  q.baseChangeAlong (Nilp.quotientO O A)

@[simp]
theorem reduction_hom (q : QuasiIsogeny F E E' h) :
    q.reduction.hom = RationalHom.reduction q.hom := rfl

@[simp]
theorem reduction_inv (q : QuasiIsogeny F E E' h) :
    q.reduction.inv = RationalHom.reduction q.inv := rfl

/-- Forgetting the order identifies the entire reduced ambient quasi-isogeny. -/
@[simp]
theorem toAtlas_reduction (q : QuasiIsogeny F E E' h) :
    q.reduction.toAtlasQuasiIsogeny = q.toAtlasQuasiIsogeny.reduction :=
  toAtlas_baseChangeAlong q (Nilp.quotientO O A)

@[simp]
theorem reduction_refl (E : OrderAction D X) :
    (refl (F := F) E).reduction = refl E.reduction :=
  baseChangeAlong_refl E (Nilp.quotientO O A)

@[simp]
theorem reduction_symm (q : QuasiIsogeny F E E' h) :
    q.symm.reduction = q.reduction.symm :=
  baseChangeAlong_symm q (Nilp.quotientO O A)

@[simp]
theorem reduction_trans (q : QuasiIsogeny F E E' h) (f : QuasiIsogeny F E' E'' k) :
    (q.trans f).reduction = q.reduction.trans f.reduction :=
  baseChangeAlong_trans q f (Nilp.quotientO O A)

@[simp]
theorem reduction_ofIso (q : Iso E E' h) :
    (ofIso (F := F) q).reduction = ofIso q.reduction :=
  baseChangeAlong_ofIso q (Nilp.quotientO O A)

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
