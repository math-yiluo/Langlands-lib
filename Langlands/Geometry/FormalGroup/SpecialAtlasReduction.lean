import Langlands.Geometry.FormalGroup.SpecialAtlasBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderReduction

/-! # Reduction of actual special formal division-order atlases -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R] {r : R}
variable {A : Nilp.{v, w} R r}

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X Y : SpecialAtlas K D ι A.obj}
variable {h : X.atlas.opens = Y.atlas.opens}

/-- Extend the actual special atlas along the canonical principal-ideal quotient. -/
def reduction (X : SpecialAtlas K D ι A.obj) :
    SpecialAtlas K D ι ((Nilp.reductionFunctor R r).obj A).obj :=
  X.baseChangeAlong (Nilp.quotientO 𝒪[K] A)

/-- The reduced atlas is precisely the ambient quotient extension. -/
@[simp]
theorem reduction_atlas (X : SpecialAtlas K D ι A.obj) :
    X.reduction.atlas = X.atlas.reduction := rfl

/-- The reduced action extends every element of the actual division order. -/
@[simp]
theorem reduction_order (X : SpecialAtlas K D ι A.obj) :
    X.reduction.order = X.order.reduction := rfl

/-- The reduced principal cover consists exactly of the images of the original generators. -/
@[simp]
theorem reduction_opens (X : SpecialAtlas K D ι A.obj) :
    X.reduction.atlas.opens = (Nilp.quotientO 𝒪[K] A) '' X.atlas.opens := rfl

/-- The same embedded unramified subfield certificate is retained. -/
@[simp]
theorem reduction_unramified (X : SpecialAtlas K D ι A.obj) :
    X.reduction.unramified = X.unramified := rfl

/-- Reduction preserves the supplied actual height-d² certificate and base nilpotence. -/
theorem reduction_height (X : SpecialAtlas K D ι A.obj) {π : 𝒪[K]}
    (hX : X.HasHeightSquared π) : X.reduction.HasHeightSquared π :=
  X.baseChangeAlong_height (Nilp.quotientO 𝒪[K] A) hX

/-- Reduced complete families are the original families on quotient-algebra tests. -/
def reductionPointEquiv (X : SpecialAtlas K D ι A.obj)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj) :
    X.Point (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B) ≃ₗ[IntegerRing K D]
      X.reduction.Point B :=
  X.order.reductionPointEquiv B

/-- Forgetting the full order retains the ambient whole-family quotient comparison. -/
theorem reductionPointEquiv_eq (X : SpecialAtlas K D ι A.obj)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B)) :
    X.reductionPointEquiv B x = X.atlas.reductionPointEquiv B x :=
  X.order.reductionPointEquiv_eq B x

/-- The division-order-linear whole-family comparison is natural in all further tests. -/
theorem reductionPointEquiv_natural (X : SpecialAtlas K D ι A.obj)
    {B C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj} (f : B ⟶ C)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B)) :
    X.reduction.order.mapPoints f (X.reductionPointEquiv B x) =
      X.reductionPointEquiv C
        (X.order.mapPoints (restrictCoefficientMap (Nilp.quotientO 𝒪[K] A) f) x) :=
  X.order.reductionPointEquiv_natural f x

/-- Natural comparison of the actual division-order-module point functors on reduced tests. -/
def reductionPointFunctorIso (X : SpecialAtlas K D ι A.obj) :
    restrictCoefficientFunctor (Nilp.quotientO 𝒪[K] A) ⋙ X.pointFunctor ≅
      X.reduction.pointFunctor :=
  X.order.reductionPointFunctorIso

/-- Reduce an actual same-cover division-order-linear formal map. -/
def reductionHom (f : X.Hom Y h) :
    X.reduction.Hom Y.reduction (BasicAtlas.reductionOpens_eq h) :=
  f.reduction

/-- Forgetting order commutation retains exactly the ambient reduced formal map. -/
@[simp]
theorem reductionHom_val (f : X.Hom Y h) :
    (reductionHom f).val = f.val.reduction :=
  f.reduction_val

/-- The actual reduced formal map realizes the forward complete-family square. -/
theorem reductionHom_onPoints (f : X.Hom Y h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B)) :
    (reductionHom f).onPoints B (X.reductionPointEquiv B x) =
      Y.reductionPointEquiv B
        (f.onPoints (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B) x) :=
  f.reduction_onPoints B x

/-- The same reduced formal map realizes the inverse complete-family square. -/
theorem reductionHom_fromPoints (f : X.Hom Y h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (y : X.reduction.Point B) :
    f.onPoints (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B)
        ((X.reductionPointEquiv B).symm y) =
      (Y.reductionPointEquiv B).symm ((reductionHom f).onPoints B y) :=
  f.reduction_fromPoints B y

/-- Reduce both actual full-order formal maps and their two inverse equations. -/
def reductionIso (f : X.Iso Y h) :
    X.reduction.Iso Y.reduction (BasicAtlas.reductionOpens_eq h) :=
  f.reduction

@[simp]
theorem reductionIso_hom (f : X.Iso Y h) :
    (reductionIso f).hom = reductionHom f.hom :=
  f.reduction_hom

@[simp]
theorem reductionIso_inv (f : X.Iso Y h) :
    (reductionIso f).inv = reductionHom f.inv :=
  f.reduction_inv

/-- The reduced actual isomorphism realizes the forward complete-family square. -/
theorem reductionIso_onPoints (f : X.Iso Y h)
    (B : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B)) :
    (reductionIso f).onPoints B (X.reductionPointEquiv B x) =
      Y.reductionPointEquiv B
        (f.onPoints (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) B) x) :=
  f.reduction_onPoints B x

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
