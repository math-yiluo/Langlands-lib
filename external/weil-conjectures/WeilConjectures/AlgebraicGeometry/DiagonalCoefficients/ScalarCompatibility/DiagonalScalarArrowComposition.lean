/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars

/-! # Composition of supplied scalar arrow squares

Source: diagonal tower coefficient changes (1), the two scalar delta squares.
(blueprint: lem-diagonal-scalar-arrow-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients.ScalarCompatibility

attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local instance 100001]
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] derivedScalars Endpoint.shift DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

/-- Derived scalar adjunction, retaining its coefficient objects as parameters. -/
@[irreducible] def scalarAdjunction
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u}) :
    derivedScalars a X ⊣ (Mod.comap (coefficientMap a X)).mapDerivedCategory := by
  unfold derivedScalars
  exact @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (condensedRingObj R X) (condensedRingObj S X) _ _
    (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj S X)
    (coefficientMap a X) _

variable {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
  [MonObj R₂] [IsCommMonObj R₂]
  {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b]
  {Y : Scheme.{u}}
  {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
  {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
  {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
  {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
  {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
  {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
  (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
  (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂)

/-- The successive left functor with the coefficient choices of the supplied squares. -/
abbrev compositeFunctor (_s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (_t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂) :=
  derivedScalars a (diagonalSurface Y) ⋙ derivedScalars b (diagonalSurface Y)

/-- The ordinary restriction functor right adjoint to both scalar changes. -/
abbrev compositeRestriction (_s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
    (_t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂) :
    Modules R₂ (diagonalSurface Y) ⥤ Modules R₀ (diagonalSurface Y) :=
  Mod.comap (coefficientMap b (diagonalSurface Y)) ⋙
    Mod.comap (coefficientMap a (diagonalSurface Y))

/-- The actual successive scalar adjunction, with its exact right functor collected. -/
@[irreducible] def compositeAdjunction :
    compositeFunctor s t ⊣ (compositeRestriction s t).mapDerivedCategory :=
  ((scalarAdjunction a (diagonalSurface Y)).comp
    (scalarAdjunction b (diagonalSurface Y))).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso
        (Mod.comap (coefficientMap b (diagonalSurface Y)))
        (Mod.comap (coefficientMap a (diagonalSurface Y))))

/-- The supported endpoint for two successive scalar changes. -/
def compositeSource :
    (compositeFunctor s t).obj
      ((DerivedCategory.singleFunctor _ 0).obj (source R₀ Y)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (source R₂ Y) :=
  (derivedScalars b (diagonalSurface Y)).mapIso s.supported.iso ≪≫ t.supported.iso

/-- The degree-two line endpoint for two successive scalar changes. -/
def compositeTarget :
    (compositeFunctor s t).obj
      (((DerivedCategory.singleFunctor _ 0).obj (L₀ (diagonalSurface Y)))⟦(2 : ℤ)⟧) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj (L₂ (diagonalSurface Y)))⟦(2 : ℤ)⟧ :=
  (derivedScalars b (diagonalSurface Y)).map (s.lineW.shift a) ≫ t.lineW.shift b

/-- Map the first delta square through the second scalar functor, and then use the
second delta square. All coefficient rings and line objects remain parameters. -/
theorem composite_delta :
    (compositeFunctor s t).map
      d₀.delta ≫ compositeTarget s t = (compositeSource s t).hom ≫ d₂.delta := by
  have h := congrArg
    (fun k ↦ (derivedScalars b (diagonalSurface Y)).map k ≫ t.lineW.shift b) s.delta
  unfold compositeFunctor compositeSource compositeTarget
  simpa only [Functor.map_comp, Functor.comp_map, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, t.delta] using h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients.ScalarCompatibility
