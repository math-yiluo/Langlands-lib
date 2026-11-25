/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorOrdinarySquare
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorSummandFormulas

/-! # Signed total scalar section tensor square

## References

* Stacks, Cohomology on Sites, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

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

attribute [local irreducible] Mod.extendScalars CondensedRing.internalScalarMonoidal
  ordinaryTensorComparison totalComparison totalScalar
attribute [local irreducible] HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

-- Check all summands without expanding the derived tensor structures.
/-- Totalization of the ordinary scalar section tensor square.
Check every summand of the unbounded direct-sum total. The ordinary scalar square,
the defining total comparison formulas and the assumed summand formula for g give
the same composite, by naturality of the termwise scalar comparison. -/
theorem section_tensor_total_scalar_square (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
      (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
        (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
        (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) =
      sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
        (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s))
    (P Q : CochainComplex (Modules Λ T) ℤ)
    (g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj
        ((((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ⊗
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)) ⟶
      (c.model.E.mapHomologicalComplex (.up ℤ)).obj
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (c.model.E.mapHomologicalComplex (.up ℤ)).obj
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))
    (hg : ∀ (i j k : ℤ) (h : i + j = k),
      c.model.E.map
        (HomologicalComplex.ιTensorObj
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q) i j k h) ≫
        g.f k =
      (e.app ((equivalence Λ T).functor.obj (P.X i))).app
          ((equivalence Λ T).functor.obj (Q.X j)) ≫
        HomologicalComplex.ιTensorObj
          ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P))
          ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)) i j k h) :
    let F := (extension a T).mapHomologicalComplex (.up ℤ)
    let ES := (equivalence Λ' T).functor.mapHomologicalComplex (.up ℤ)
    let o := NatIso.mapHomologicalComplex c.ordinary (.up ℤ)
    ES.map (totalScalar a T P Q) ≫ (totalComparison Λ' T (F.obj P) (F.obj Q)).hom ≫
      (o.hom.app P ⊗ₘ o.hom.app Q) =
    o.hom.app (P ⊗ Q) ≫
      (c.model.E.mapHomologicalComplex (.up ℤ)).map (totalComparison Λ T P Q).hom ≫ g := by
  let := CondensedRing.internalScalarMonoidal a T
  let F := extension a T
  let ER := (equivalence Λ T).functor
  let ES := (equivalence Λ' T).functor
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let ESc := ES.mapHomologicalComplex (.up ℤ)
  let Bc := c.model.E.mapHomologicalComplex (.up ℤ)
  let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex c.ordinary (.up ℤ)
  let δ := totalScalar a T P Q
  let r := totalComparison Λ T P Q
  let s := totalComparison Λ' T (Fc.obj P) (Fc.obj Q)
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (K₁ := P) (K₂ := Q) (F := curriedTensor (Modules Λ T))
    (c := ComplexShape.up ℤ) (j := n) (F ⋙ ES)
  intro i j hij
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.comp_map]
  refine paste_summand_square ER ES F c.model.E c.ordinary
    (HomologicalComplex.ιTensorObj P Q i j n hij)
    (δ.f n) (r.hom.f n) (s.hom.f n) (g.f n)
    ((o.hom.app P ⊗ₘ o.hom.app Q).f n)
    (Functor.OplaxMonoidal.δ F (P.X i) (Q.X j))
    (ordinaryTensorComparison Λ T (P.X i) (Q.X j)).hom
    (ordinaryTensorComparison Λ' T (F.obj (P.X i)) (F.obj (Q.X j))).hom
    ((e.app (ER.obj (P.X i))).app (ER.obj (Q.X j)))
    (HomologicalComplex.ιTensorObj (Fc.obj P) (Fc.obj Q) i j n hij)
    (HomologicalComplex.ιTensorObj (ERc.obj P) (ERc.obj Q) i j n hij)
    (HomologicalComplex.ιTensorObj (ESc.obj (Fc.obj P)) (ESc.obj (Fc.obj Q)) i j n hij)
    (HomologicalComplex.ιTensorObj (Bc.obj (ERc.obj P)) (Bc.obj (ERc.obj Q)) i j n hij)
    (c.ordinary.hom.app (P.X i) ⊗ₘ c.ordinary.hom.app (Q.X j)) ?_ ?_ ?_ ?_ ?_
    (section_tensor_ordinary_scalar_square a T c hc e he (P.X i) (Q.X j))
  · exact scalar_total_summand a T P Q i j n hij
  · exact section_tensor_total_summand Λ T P Q i j n hij
  · exact section_tensor_total_summand Λ' T (Fc.obj P) (Fc.obj Q) i j n hij
  · exact hg i j n hij
  · exact summand_naturality T F ES ER c.model.E
      c.ordinary P Q i j n hij

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
