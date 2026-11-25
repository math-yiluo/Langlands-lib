/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAugmentation
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Normalized cone boundary and quotient-linear coinduction trace

Source: Stacks Tags 06YP, 06YY and 07A6; the connecting morphism of the principal-resolution
triangle and adjoint transposition.
(blueprint: lem-sf-regular-quotient-cone-boundary). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [EssentiallySmall.{r} C]
  {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  {t : (unit (derivedChangeRingIndependentCoefficients J R)).sections}
  {d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ}

/-- The strict cone projection, natural for every chain map.
Source: Stacks Tags 06YP, 06YY and 07A6; the connecting morphism of the principal-resolution
triangle and adjoint transposition.
(blueprint: lem-sf-regular-quotient-cone-boundary). -/
def chainBoundary : cone R t ⟶ shiftFunctor (CochainComplex (Modules R) ℤ) (1 : ℤ) where
  app P := (CochainComplex.mappingCone.triangle ((complexScalar R t).app P)).mor₃
  naturality {P Q} f :=
    (CochainComplex.mappingCone.triangleMap ((complexScalar R t).app P)
      ((complexScalar R t).app Q) f f ((complexScalar R t).naturality f).symm).comm₃.symm

/-- Descend the strict mapping-cone boundary through localization, then use the
normalized augmentation to identify its domain with extension followed by restriction.
Source: Stacks Tags 06YP, 06YY and 07A6; the connecting morphism of the principal-resolution
triangle and adjoint transposition.
(blueprint: lem-sf-regular-quotient-cone-boundary). -/
def Augmentation.boundary (b : Augmentation φ t d) :
    d.T ⋙ b.V ⟶ shiftFunctor (DerivedCategory (Modules R)) (1 : ℤ) := by
  let Q := DerivedCategory.Q (C := Modules R)
  let W := HomologicalComplex.quasiIso (Modules R) (.up ℤ)
  let H := shiftFunctor (DerivedCategory (Modules R)) (1 : ℤ)
  let β : Q ⋙ b.D ⟶ Q ⋙ H :=
    b.cone_factor.hom ≫ Functor.whiskerRight (chainBoundary (R := R) (t := t)) Q ≫
      (Q.commShiftIso (1 : ℤ)).hom
  exact b.A.inv ≫ Localization.liftNatTrans Q W (Q ⋙ b.D) (Q ⋙ H) b.D H β

/-- Shift the source of the boundary back by one, giving the trace before transposition.
Source: Stacks Tags 06YP, 06YY and 07A6; the connecting morphism of the principal-resolution
triangle and adjoint transposition.
(blueprint: lem-sf-regular-quotient-cone-boundary). -/
def Augmentation.traceCounit (b : Augmentation φ t d) :
    (shiftFunctor (DerivedCategory (Modules R)) (-1 : ℤ) ⋙ d.T) ⋙ b.V ⟶ 𝟭 _ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (shiftFunctor _ (-1 : ℤ)) b.boundary ≫
      (shiftFunctorCompIsoId (DerivedCategory (Modules R)) (-1 : ℤ) 1 (by omega)).hom

/-- Transposition makes the cone trace linear over the quotient coefficient sheaf.
Source: Stacks Tags 06YP, 06YY and 07A6; the connecting morphism of the principal-resolution
triangle and adjoint transposition.
(blueprint: lem-sf-regular-quotient-cone-boundary). -/
def Augmentation.coinductionTrace (b : Augmentation φ t d)
    {G : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S)} (a : b.V ⊣ G) :
    shiftFunctor (DerivedCategory (Modules R)) (-1 : ℤ) ⋙ d.T ⟶ G where
  app K := a.homEquiv _ _ (b.traceCounit.app K)
  naturality {K L} f := by
    rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
    exact congrArg (a.homEquiv _ _) (b.traceCounit.naturality f)

end SheafOfModules.RegularQuotientCone
