/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Input and internal scalar-total path

## References

* Stacks 03EL, 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

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

/-- The invertible input identification from internal derived tensors to section tensors. -/
def scalarTensorSectionInput (T : Scheme.{u}) (c : ScalarSectionData a T)
    (P Q : CochainComplex (Modules Λ T) ℤ) :
    (derivedFunctor Λ' T).obj
        ((D a T).obj (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q)) ⟶
      c.model.T.obj ((tensor Λ T).obj
        (DerivedCategory.Q.obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P),
          DerivedCategory.Q.obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))) :=
  c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
    c.model.T.map ((tensorComparison Λ T).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
    c.model.T.map ((tensor Λ T).map (Prod.mkHom
      (sectionLocalizationComparison Λ T P).hom (sectionLocalizationComparison Λ T Q).hom))

/-- The concrete internal scalar-total path, followed by the ordinary section comparisons. -/
def scalarTensorSectionPath (T : Scheme.{u}) (c : ScalarSectionData a T)
    (P Q : CochainComplex (Modules Λ T) ℤ) :
    (derivedFunctor Λ' T).obj
        ((D a T).obj (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalTensor Λ' T).obj
        ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P),
          (c.model.E.mapHomologicalComplex (.up ℤ)).obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))) :=
  letI : (DerivedCategory.Q (C := Modules Λ T)).LaxMonoidal := Mod.laxMonoidalQ
  let σ := Functor.mapHomologicalComplexCompIso c.ordinary (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl ((equivalence Λ T).functor ⋙ c.model.E)) (.up ℤ)).symm
  (derivedFunctor Λ' T).map
      ((D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        compute a T (P ⊗ Q) ≫ DerivedCategory.Q.map (totalScalar a T P Q)) ≫
    localizedTotalComparison Λ' T
      (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
      (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q) ≫
    DerivedCategory.Q.map ((totalTensor Λ' T).map
      (Prod.mkHom (σ.hom.app P) (σ.hom.app Q)))

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
