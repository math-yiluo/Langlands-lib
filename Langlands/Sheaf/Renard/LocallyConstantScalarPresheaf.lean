import Langlands.Sheaf.Renard.BasisPresheaf
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Algebra.Category.Ring.Basic

/-! # Actual locally constant scalar ring presheaves -/

open CategoryTheory Opposite TopologicalSpace

universe u r

namespace Langlands.Sheaf.Renard.LocallyConstantScalar

variable {X : Type u} [TopologicalSpace X]

/-- The actual continuous inclusion of one open subset in another. -/
def inclusion {U V : Opens X} (h : U ≤ V) : C(U, V) where
  toFun x := ⟨x.val, h x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Restriction is Mathlib's pullback unital ring homomorphism. -/
def restrict (R : Type r) [Ring R] {U V : Opens X} (h : U ≤ V) :
    LocallyConstant V R →+* LocallyConstant U R :=
  LocallyConstant.comapRingHom (inclusion h)

@[simp]
theorem restrict_apply (R : Type r) [Ring R] {U V : Opens X} (h : U ≤ V)
    (s : LocallyConstant V R) (x : U) :
    restrict R h s x = s ⟨x.val, h x.property⟩ := rfl

@[simp]
theorem restrict_id (R : Type r) [Ring R] (U : Opens X) :
    restrict R (le_refl U) = RingHom.id (LocallyConstant U R) := by
  ext s x
  rfl

/-- The pointwise pullbacks satisfy the contravariant composition law. -/
theorem restrict_comp (R : Type r) [Ring R] {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (restrict R hUV).comp (restrict R hVW) = restrict R (hUV.trans hVW) := by
  ext s x
  rfl

/-- The actual locally constant section rings on all opens of the supplied topology. -/
def ringPresheaf (X : Type u) [TopologicalSpace X] (R : Type r) [Ring R] :
    (Opens X)ᵒᵖ ⥤ RingCat.{max u r} where
  obj U := RingCat.of (LocallyConstant U.unop R)
  map f := RingCat.ofHom (restrict R f.unop.le)
  map_id U := by
    apply RingCat.hom_ext
    exact restrict_id R U.unop
  map_comp f g := by
    apply RingCat.hom_ext
    exact (restrict_comp R g.unop.le f.unop.le).symm

@[simp]
theorem ringPresheaf_obj (R : Type r) [Ring R] (U : Opens X) :
    (ringPresheaf X R).obj (op U) = RingCat.of (LocallyConstant U R) := rfl

@[simp]
theorem ringPresheaf_map (R : Type r) [Ring R] {U V : Opens X} (h : U ≤ V) :
    ((ringPresheaf X R).map (homOfLE h).op).hom = restrict R h := rfl

/-- Restrict the all-open ring presheaf by the published inclusion of a chosen basis. -/
def basisRingPresheaf (B : OpenBasis X) (R : Type r) [Ring R] :
    (BasisOpen B)ᵒᵖ ⥤ RingCat.{max u r} :=
  (basisInclusion B).op ⋙ ringPresheaf X R

/-- The underlying abelian presheaf is the actual forgetful composite. -/
def rawPresheaf (B : OpenBasis X) (R : Type r) [Ring R] : RawPresheaf.{u,max u r} B :=
  basisRingPresheaf B R ⋙ forget₂ RingCat AddCommGrpCat

@[simp]
theorem basisRingPresheaf_obj (B : OpenBasis X) (R : Type r) [Ring R]
    (U : BasisOpen B) :
    (basisRingPresheaf B R).obj (op U) = RingCat.of (LocallyConstant U.obj R) := rfl

@[simp]
theorem rawPresheaf_sections (B : OpenBasis X) (R : Type r) [Ring R]
    (U : BasisOpen B) :
    Sections (rawPresheaf B R) U = AddCommGrpCat.of (LocallyConstant U.obj R) := rfl

@[simp]
theorem rawPresheaf_restriction (B : OpenBasis X) (R : Type r) [Ring R]
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    (restriction (rawPresheaf B R) h).hom = (restrict R h).toAddMonoidHom := rfl

end Langlands.Sheaf.Renard.LocallyConstantScalar
