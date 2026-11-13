import Langlands.Geometry.FormalGroup.NilpotentReduction
import Langlands.Geometry.FormalGroup.CoefficientCoherence

/-! # Reduction of formal O-modules on nilpotent coefficient algebras -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

open CategoryTheory

variable (O : Type u) [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {π : R}

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

namespace Nilp

variable {A B C : Nilp.{v, w} R π}

/-- A morphism of coefficient R-algebras is a morphism for the structural O-algebras. -/
def scalarMap (f : A ⟶ B) : A.obj →ₐ[O] B.obj := f.hom.hom.restrictScalars O

/-- The actual quotient map A → A/(π), regarded as an O-algebra map. -/
def quotientO (A : Nilp.{v, w} R π) :
    A.obj →ₐ[O] ((reductionFunctor R π).obj A).obj :=
  scalarMap O ((reductionNatTrans R π).app A)

/-- The induced map A/(π) → B/(π), regarded as an O-algebra map. -/
def reducedScalarMap (f : A ⟶ B) :
    ((reductionFunctor R π).obj A).obj →ₐ[O] ((reductionFunctor R π).obj B).obj :=
  scalarMap O ((reductionFunctor R π).map f)

@[simp]
theorem scalarMap_id (A : Nilp.{v, w} R π) :
    scalarMap O (𝟙 A) = AlgHom.id O A.obj := rfl

@[simp]
theorem scalarMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    scalarMap O (f ≫ g) = (scalarMap O g).comp (scalarMap O f) := rfl

/-- The quotient square commutes as a square of O-algebra maps. -/
theorem quotientO_natural (f : A ⟶ B) :
    (quotientO O B).comp (scalarMap O f) =
      (reducedScalarMap O f).comp (quotientO O A) := by
  apply AlgHom.ext
  intro a
  rfl

@[simp]
theorem quotientO_uniformizer (A : Nilp.{v, w} R π) :
    quotientO O A (algebraMap R A.obj π) = 0 := reductionQuotient_uniformizer π A.obj

end Nilp

namespace ModuleLaw

variable {O}
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {A B : Nilp.{v, w} R π}
variable {M : ModuleLaw O A.obj σ} {N : ModuleLaw O A.obj τ}
variable {P : ModuleLaw O A.obj υ}

/-- Reduce the actual group and scalar-action coefficients modulo π. -/
def reduction (M : ModuleLaw O A.obj σ) :
    ModuleLaw O ((Nilp.reductionFunctor R π).obj A).obj σ :=
  M.map (Nilp.quotientO O A)

/-- Reduction on integral O-linear formal homomorphisms. -/
def Hom.reduction (f : Hom M N) : Hom M.reduction N.reduction :=
  f.map (Nilp.quotientO O A)

@[simp]
theorem Hom.reduction_id : (Hom.id M).reduction = Hom.id M.reduction :=
  Hom.map_id _

@[simp]
theorem Hom.reduction_comp (g : Hom N P) (f : Hom M N) :
    (g.comp f).reduction = g.reduction.comp f.reduction := Hom.map_comp _ g f

/-- Reduction on actual integral isomorphisms. -/
def Iso.reduction (f : Iso M N) : Iso M.reduction N.reduction :=
  f.map (Nilp.quotientO O A)

namespace RationalHom

variable {F : Type*} [Field F] [Algebra O F]

/-- Reduction is F-linear on the actual tensor-product rational Hom. -/
def reduction : RationalHom F M N →ₗ[F] RationalHom F M.reduction N.reduction :=
  map (Nilp.quotientO O A)

@[simp]
theorem reduction_tmul (a : F) (f : Hom M N) :
    reduction (a ⊗ₜ[O] f) = a ⊗ₜ[O] f.reduction := map_tmul _ a f

@[simp]
theorem reduction_id : reduction (id (F := F) M) = id M.reduction := map_id _

@[simp]
theorem reduction_comp (g : RationalHom F N P) (f : RationalHom F M N) :
    reduction (comp g f) = comp (reduction g) (reduction f) := map_comp _ g f

end RationalHom

namespace QuasiIsogeny

variable {F : Type*} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Reduce both rational maps of a quasi-isogeny, preserving the inverse equations. -/
def reduction (f : QuasiIsogeny F M N) : QuasiIsogeny F M.reduction N.reduction :=
  f.map (Nilp.quotientO O A)

@[simp]
theorem reduction_refl : (refl (F := F) M).reduction = refl M.reduction := map_refl _

@[simp]
theorem reduction_symm (f : QuasiIsogeny F M N) : f.symm.reduction = f.reduction.symm := rfl

@[simp]
theorem reduction_trans (f : QuasiIsogeny F M N) (g : QuasiIsogeny F N P) :
    (f.trans g).reduction = f.reduction.trans g.reduction := map_trans f g _

@[simp]
theorem reduction_ofIso (f : Iso M N) :
    (ofIso (F := F) f).reduction = ofIso f.reduction := map_ofIso f _

end QuasiIsogeny

/-- Changing a Nilp algebra and then reducing agrees with reducing first. -/
def reductionBaseChangeIso (M : ModuleLaw O A.obj σ) (f : A ⟶ B) :
    Iso (M.map (Nilp.scalarMap O f)).reduction
      (M.reduction.map (Nilp.reducedScalarMap O f)) :=
  mapSquareIso M (Nilp.scalarMap O f) (Nilp.quotientO O B)
    (Nilp.quotientO O A) (Nilp.reducedScalarMap O f) (Nilp.quotientO_natural O f)

/-- The reduction/base-change comparison is natural in integral formal maps. -/
theorem Hom.reductionBaseChange_natural (g : Hom M N) (f : A ⟶ B) :
    (g.reduction.map (Nilp.reducedScalarMap O f)).comp (reductionBaseChangeIso M f).hom =
      (reductionBaseChangeIso N f).hom.comp (g.map (Nilp.scalarMap O f)).reduction :=
  mapSquareIso_natural g _ _ _ _ _

namespace RationalHom

variable {F : Type*} [Field F] [Algebra O F]

/-- The reduction/base-change square also commutes on actual rational Hom. -/
theorem reductionBaseChange_natural (g : RationalHom F M N) (f : A ⟶ B) :
    comp (map (Nilp.reducedScalarMap O f) (reduction g))
        (ofHom (reductionBaseChangeIso M f).hom) =
      comp (ofHom (reductionBaseChangeIso N f).hom)
        (reduction (map (Nilp.scalarMap O f) g)) :=
  mapSquareIso_natural g _ _ _ _ _

end RationalHom

namespace QuasiIsogeny

variable {F : Type*} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Reduction/base-change comparisons commute with actual quasi-isogenies. -/
theorem reductionBaseChange_natural (g : QuasiIsogeny F M N) (f : A ⟶ B) :
    (ofIso (reductionBaseChangeIso M f)).trans
        (g.reduction.map (Nilp.reducedScalarMap O f)) =
      (g.map (Nilp.scalarMap O f)).reduction.trans (ofIso (reductionBaseChangeIso N f)) :=
  mapSquareIso_natural g _ _ _ _ _

end QuasiIsogeny

end ModuleLaw

end Langlands.FormalGroup
