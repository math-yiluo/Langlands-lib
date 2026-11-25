/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Transport of one quotient tensor equation along representative isomorphisms

## References

* Stacks 06YS and 06YU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- Transport a single representative tensor equation to a fixed derived pair. -/
theorem tensor_section_condition_transport_iso
    (T : Scheme.{u}) (c : ScalarSectionData a T) (b : TensorIso a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (P Q : CochainComplex (Modules Λ T) ℤ)
    (M N : DerivedCategory (Modules Λ T))
    (eP : DerivedCategory.Q.obj P ≅ M)
    (eQ : DerivedCategory.Q.obj Q ≅ N)
    (h :
      (derivedFunctor Λ' T).map (b.hom.app (DerivedCategory.Q.obj P,
          DerivedCategory.Q.obj Q)) ≫
          (tensorComparison Λ' T).hom.app ((D a T).obj (DerivedCategory.Q.obj P),
            (D a T).obj (DerivedCategory.Q.obj Q)) =
        c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
          c.model.T.map ((tensorComparison Λ T).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          barB.hom.app ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj P),
            (derivedFunctor Λ T).obj (DerivedCategory.Q.obj Q)) ≫
          (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app (DerivedCategory.Q.obj P))
            (c.derived.inv.app (DerivedCategory.Q.obj Q)))) :
      (derivedFunctor Λ' T).map (b.hom.app (M, N)) ≫
          (tensorComparison Λ' T).hom.app ((D a T).obj M, (D a T).obj N) =
        c.derived.hom.app (M ⊗ N) ≫
          c.model.T.map ((tensorComparison Λ T).hom.app (M, N)) ≫
          barB.hom.app ((derivedFunctor Λ T).obj M,
            (derivedFunctor Λ T).obj N) ≫
          (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app M) (c.derived.inv.app N)) := by
  let lhs := Functor.whiskerRight b.hom (derivedFunctor Λ' T) ≫
    Functor.whiskerLeft ((D a T).prod (D a T)) (tensorComparison Λ' T).hom
  let rhs := Functor.whiskerLeft (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      c.derived.hom ≫
    Functor.whiskerRight (tensorComparison Λ T).hom c.model.T ≫
    Functor.whiskerLeft ((derivedFunctor Λ T).prod (derivedFunctor Λ T)) barB.hom ≫
    Functor.whiskerRight (NatTrans.prod c.derived.inv c.derived.inv) (tensor Λ' T)
  have h' : lhs.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      rhs.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := h
  change lhs.app (M, N) = rhs.app (M, N)
  rw [← lhs.naturality_1 (Iso.prod eP eQ), ← rhs.naturality_1 (Iso.prod eP eQ), h']
  rfl

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
