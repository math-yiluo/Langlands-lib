/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAdjointTower

/-! # The actual quotient coefficient tower and its tensor model

Source: Stacks Project, proetale.tex, lemma-naive-completion (099M).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
  (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)

/-- The actual finite coefficient ring on the slice. -/
abbrev adicResidueQuotientRing (n : ℕ) :=
  (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U

/-- Its rank-one module, viewed over the completed slice ring. -/
def adicResidueQuotientModule (n : ℕ) :
    Mod ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  (res (adicResidueLocalProjection.{u, v} X J U n)).obj
    (SheafOfModules.unit (siteModuleRings (adicResidueQuotientRing X J U n)))

/-- The coefficient projection commutes with the actual quotient successor. -/
theorem adicResidueQuotientProjection_step (n : ℕ) :
    adicResidueLocalProjection.{u, v} X J U (n + 1) ≫
      ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
        (transition (coefficientProEtaleModelTopology.{u, v} X) A J n) =
      adicResidueLocalProjection.{u, v} X J U n := by
  dsimp only [adicResidueLocalProjection]
  rw [← Functor.map_comp]
  congr 1
  simpa only [projection, finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
    limit.w (finiteSystem (coefficientProEtaleModelTopology.{u, v} X) A J)
      (homOfLE (Nat.le_succ n)).op

/-- The module successor is the quotient ring map, with its completed scalar action. -/
def adicResidueQuotientModuleStep (n : ℕ) :
    adicResidueQuotientModule X J U (n + 1) ⟶ adicResidueQuotientModule X J U n where
  val :=
    { app V := ModuleCat.ofHom
        (X := (adicResidueQuotientModule X J U (n + 1)).val.obj V)
        (Y := (adicResidueQuotientModule X J U n).val.obj V)
        { toFun :=
            (((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
              (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)).hom.app V
          map_add' := map_add _
          map_smul' s m := by
            let x : (adicResidueQuotientRing X J U (n + 1)).obj.obj V := m
            change
              (((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
                (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)).hom.app V
                  ((adicResidueLocalProjection.{u, v} X J U (n + 1)).hom.app V s * x) =
                (adicResidueLocalProjection.{u, v} X J U n).hom.app V s *
                  (((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
                    (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)).hom.app V x
            rw [map_mul]
            congr 1
            exact congrArg (fun f ↦ f.hom.app V s)
              (adicResidueQuotientProjection_step X J U n) }
      naturality {V W} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact congrArg (fun k ↦ k m)
          (congrArg (fun k ↦ k.hom)
            ((((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
              (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)).hom.naturality f)) }

/-- The finite coefficient tower in degree zero, with literal quotient transitions. -/
def adicResidueQuotientCoefficientTower :
    ℕᵒᵖ ⥤ Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  Functor.ofOpSequence
    (X := fun n ↦ (HomologicalComplex.single _ (.up ℤ) 0).obj
      (adicResidueQuotientModule X J U n)) (fun n ↦
    (HomologicalComplex.single _ (.up ℤ) 0).map (adicResidueQuotientModuleStep X J U n))

/-- The degree-zero quotient map from the coefficient ring. -/
def adicResidueQuotientCoefficientUnit (n : ℕ) :
    ringedSiteRingComplex
        ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) ⟶
      (adicResidueQuotientCoefficientTower X J U).obj (op n) :=
  (HomologicalComplex.single _ (.up ℤ) 0).map
    ((adicResidueQuotientModule X J U n).unitHomEquiv.symm
      ⟨fun V ↦ (1 : (adicResidueQuotientRing X J U n).obj.obj V),
        fun {V W} f ↦ by
          change (adicResidueQuotientRing X J U n).obj.map f 1 = 1
          exact map_one _⟩)

/-- Tensor the fixed complex with the actual quotient coefficients. -/
def adicResidueQuotientTensorTower
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)) :=
  adicResidueQuotientCoefficientTower X J U ⋙
    (ringedKoszulTensor
      ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)).obj P

/-- The same strict tower transposed into a complex of towers. -/
def adicResidueQuotientTensorComplex
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)) :=
  (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj
    (adicResidueQuotientTensorTower X J U P)

/-- Insertion of one into the finite quotient tensor model. -/
def adicResidueQuotientTensorUnit
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (n : ℕ) : P ⟶ (adicResidueQuotientTensorTower X J U P).obj (op n) :=
  (ringedKoszulRightUnitIso _ P).inv ≫
    ((ringedKoszulTensor _).obj P).map (adicResidueQuotientCoefficientUnit X J U n)

end AlgebraicGeometry.Scheme
