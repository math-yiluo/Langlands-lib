import Langlands.Geometry.FormalGroup.AtlasMorphism
import Langlands.Geometry.FormalGroup.AtlasRefinementPoints
import Mathlib.RingTheory.Ideal.Operations

/-! # Formal coordinate comparisons on common principal covers -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory
open scoped Pointwise

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- An isomorphism is a pair of actual formal atlas maps with formal inverse laws. -/
structure Iso (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) (h : X.opens = Y.opens) where
  hom : Hom X Y h
  inv : Hom Y X h.symm
  inv_hom : inv.comp hom = Hom.id X
  hom_inv : hom.comp inv = Hom.id Y

namespace Iso

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Evaluate the formal inverse equations on full compatible point families. -/
def onPoints (f : Iso X Y h) (A : CommAlgCat.{v} R) : X.Point A ≃ₗ[O] Y.Point A where
  toFun := f.hom.onPoints A
  invFun := f.inv.onPoints A
  map_add' := (f.hom.onPoints A).map_add
  map_smul' := (f.hom.onPoints A).map_smul
  left_inv x := by rw [← Hom.onPoints_comp, f.inv_hom, Hom.onPoints_id]
  right_inv x := by rw [← Hom.onPoints_comp, f.hom_inv, Hom.onPoints_id]

/-- Formal chart isomorphisms give a natural isomorphism on actual point functors. -/
def pointFunctorIso (f : Iso X Y h) : X.pointFunctor ≅ Y.pointFunctor :=
  NatIso.ofComponents (fun A => (f.onPoints A).toModuleIso) (by
    intro A B φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.hom.onPoints_natural φ x).symm)

/-- Restrict the same actual isomorphism to algebras where pi is nilpotent. -/
def nilpPointFunctorIso (f : Iso X Y h) (π : R) :
    X.nilpPointFunctor π ≅ Y.nilpPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) f.pointFunctorIso

/-- Identity formal coordinate comparison. -/
def refl (X : BasicAtlas O R σ) : Iso X X rfl where
  hom := Hom.id X
  inv := Hom.id X
  inv_hom := Hom.comp_id _
  hom_inv := Hom.comp_id _

/-- Reverse both actual formal maps. -/
def symm (f : Iso X Y h) : Iso Y X h.symm where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose formal coordinate comparisons on the same principal cover. -/
def trans (f : Iso X Y h) (g : Iso Y Z k) : Iso X Z (h.trans k) where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc g.inv, g.inv_hom, Hom.id_comp, f.inv_hom]
  hom_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc f.hom, f.hom_inv, Hom.id_comp, g.hom_inv]

end Iso

/-- Products of generators give a common principal-open cover of two atlases. -/
def commonOpens (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) : Set R :=
  X.opens * Y.opens

/-- The product cover still spans the unit ideal, without any finiteness assumption. -/
theorem commonOpens_covers (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) :
    Ideal.span (commonOpens X Y) = ⊤ := by
  rw [commonOpens, ← Ideal.span_mul_span, X.covers, Y.covers, Ideal.top_mul]

/-- Each product generator has two actual source charts. -/
theorem exists_commonSources (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (c : commonOpens X Y) : ∃ ab : X.opens × Y.opens, ab.1.val * ab.2.val = c.val := by
  rcases Set.mem_mul.mp c.property with ⟨a, ha, b, hb, hab⟩
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

/-- Choose factors only after passing to the set of product generators. -/
def commonSources (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (c : commonOpens X Y) : X.opens × Y.opens :=
  Classical.choose (exists_commonSources X Y c)

@[simp]
theorem commonSources_mul (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (c : commonOpens X Y) :
    (commonSources X Y c).1.val * (commonSources X Y c).2.val = c.val :=
  Classical.choose_spec (exists_commonSources X Y c)

/-- The product chart is actually contained in its chosen left original chart. -/
theorem commonLeft_unit (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (c : commonOpens X Y) :
    IsUnit (algebraMap R (Localization.Away c.val) (commonSources X Y c).1.val) := by
  apply isUnit_of_mul_isUnit_left (y :=
    algebraMap R (Localization.Away c.val) (commonSources X Y c).2.val)
  rw [← map_mul, commonSources_mul]
  exact IsLocalization.Away.algebraMap_isUnit c.val

/-- The product chart is actually contained in its chosen right original chart. -/
theorem commonRight_unit (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (c : commonOpens X Y) :
    IsUnit (algebraMap R (Localization.Away c.val) (commonSources X Y c).2.val) := by
  apply isUnit_of_mul_isUnit_right (x :=
    algebraMap R (Localization.Away c.val) (commonSources X Y c).1.val)
  rw [← map_mul, commonSources_mul]
  exact IsLocalization.Away.algebraMap_isUnit c.val

/-- Restrict the left actual atlas to the product principal cover. -/
def commonLeft (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) : CoverRefinement X where
  opens := commonOpens X Y
  covers := commonOpens_covers X Y
  source c := (commonSources X Y c).1
  contains := commonLeft_unit X Y

/-- Restrict the right actual atlas to the same product principal cover. -/
def commonRight (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) : CoverRefinement Y where
  opens := commonOpens X Y
  covers := commonOpens_covers X Y
  source c := (commonSources X Y c).2
  contains := commonRight_unit X Y

/-- A comparison is actual formal coordinate isomorphism data after refinement. -/
structure Comparison (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) where
  left : CoverRefinement X
  right : CoverRefinement Y
  sameCover : left.opens = right.opens
  coordinateIso : Iso left.atlas right.atlas sameCover

namespace Comparison

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}

/-- Refine, apply the formal coordinate isomorphism, then glue the right family. -/
def onPoints (f : Comparison X Y) (A : CommAlgCat.{v} R) : X.Point A ≃ₗ[O] Y.Point A :=
  ((f.left.pointEquiv A).trans (f.coordinateIso.onPoints A)).trans (f.right.pointEquiv A).symm

/-- Actual coordinate comparison across different covers is natural on point functors. -/
def pointFunctorIso (f : Comparison X Y) : X.pointFunctor ≅ Y.pointFunctor :=
  (f.left.pointFunctorIso.trans f.coordinateIso.pointFunctorIso).trans
    f.right.pointFunctorIso.symm

/-- The different-cover comparison restricts to actual Nilp algebras. -/
def nilpPointFunctorIso (f : Comparison X Y) (π : R) :
    X.nilpPointFunctor π ≅ Y.nilpPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) f.pointFunctorIso

/-- Build a comparison using the actual common product cover. -/
def ofCommon (f : Iso (commonLeft X Y).atlas (commonRight X Y).atlas rfl) :
    Comparison X Y where
  left := commonLeft X Y
  right := commonRight X Y
  sameCover := rfl
  coordinateIso := f

end Comparison

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
