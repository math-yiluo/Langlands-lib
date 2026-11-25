/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Resolution extension for quotient section tensor equations

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

/-- Flat-term representative equations extend uniquely to all derived pairs. -/
theorem tensor_section_condition_of_kflat
    (T : Scheme.{u}) (c : ScalarSectionData a T) (b : TensorIso a T)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hK : ∀ (P Q : CochainComplex (Modules Λ T) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
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
    TensorSectionCondition a T c b barB := by
  intro M N
  let M₀ := DerivedCategory.Q.objPreimage M
  let N₀ := DerivedCategory.Q.objPreimage N
  let eM : DerivedCategory.Q.obj M₀ ≅ M := DerivedCategory.Q.objObjPreimageIso M
  let eN : DerivedCategory.Q.obj N₀ ≅ N := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨P, p, hpqi, hpflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat M₀
  obtain ⟨Q, q, hqqi, hqflat, hQ⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat N₀
  let eP : DerivedCategory.Q.obj P ≅ M :=
    asIso (DerivedCategory.Q.map p) ≪≫ eM
  let eQ : DerivedCategory.Q.obj Q ≅ N :=
    asIso (DerivedCategory.Q.map q) ≪≫ eN
  exact tensor_section_condition_transport_iso a T c b barB P Q M N eP eQ
    (hK P Q hP hQ hpflat hqflat)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
