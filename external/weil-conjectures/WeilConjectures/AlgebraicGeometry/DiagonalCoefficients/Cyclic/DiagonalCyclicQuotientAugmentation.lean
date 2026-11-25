/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicEvaluationEndpoints
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit

/-! # The actual underlying cyclic quotient unit

Source: coefficient changes (1), the scalar-extension adjunction.
(blueprint: def-diagonal-cyclic-quotient-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local semireducible] cyclicDiscreteRestriction

attribute [local irreducible] Functor.mapDerivedCategory derivedScalars
  cyclicEvaluationFunctor cyclicFiniteEvaluationFunctor

/-- Finite realization and scalar restriction retain the same underlying sheaf.
Source: finite realization's underlying comparison and exact scalar restriction
(blueprint: def-diagonal-cyclic-quotient-augmentation). -/
def cyclicFiniteUnderlying (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    (p : CyclicCartierFrame l Y n) :
    p.eW.F ⋙ diagonalFiniteToPadic l n (diagonalSurface Y) ⋙
        diagonalForget l (diagonalSurface Y) ≅ Mod.forget _ :=
  Functor.isoWhiskerLeft p.eW.F
    (diagonalFiniteForgetIso l n (diagonalSurface Y)).symm ≪≫ p.eW.underlying

/-- Exact-functor comparison before applying the scalar adjunction unit.
Source: completed realization's specified underlying comparison
(blueprint: def-diagonal-cyclic-quotient-augmentation). -/
def cyclicCompletedUnderlying (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) :
    cyclicDiscreteRestriction l (diagonalSurface Y) ⋙
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory ≅
      eW.F.mapDerivedCategory ⋙ (Mod.forget _).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (diagonalCompletedRestriction l (diagonalSurface Y))
    (diagonalForget l (diagonalSurface Y))) ≪≫
    Functor.mapDerivedCategoryNatIso eW.underlying.symm ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The underlying cyclic evaluation is the derived scalar quotient followed by
forgetting its finite action. Source: exact-functor composition and finite realization
(blueprint: def-diagonal-cyclic-quotient-augmentation). -/
def cyclicEvaluationUnderlying (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    cyclicEvaluationFunctor l Y n eW p ⋙
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory ≅
      eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y) ⋙
        (Mod.forget _).mapDerivedCategory := by
  let H := diagonalFiniteToPadic l n (diagonalSurface Y)
  let U := diagonalForget l (diagonalSurface Y)
  let f := Functor.isoWhiskerLeft p.eW.F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso H U) ≪≫
    (Functor.mapDerivedCategoryCompIso p.eW.F (H ⋙ U)) ≪≫
    Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)
  unfold cyclicEvaluationFunctor cyclicFiniteEvaluationFunctor
  exact Functor.isoWhiskerLeft
    (eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y)) f

/-- The underlying unit of derived scalar extension.
Source: the actual scalar adjunction
(blueprint: def-diagonal-cyclic-quotient-augmentation). -/
def scalarUnderlyingUnit
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)] :
    (Mod.forget (condensedRingObj Λ X)).mapDerivedCategory ⟶
      derivedScalars a X ⋙ (Mod.forget (condensedRingObj Λ' X)).mapDerivedCategory := by
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)
  let R : Modules Λ' X ⥤ Modules Λ X := Mod.comap (coefficientMap a X)
  let adj : derivedScalars a X ⊣ R.mapDerivedCategory := by
    unfold derivedScalars
    exact @Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (condensedRingObj Λ X) (condensedRingObj Λ' X) _ _
      (isCommMonObj_condensedRingObj Λ X) (isCommMonObj_condensedRingObj Λ' X)
      (coefficientMap a X) _
  let r : (R ⋙ U).mapDerivedCategory ≅
      (Mod.forget (condensedRingObj Λ' X)).mapDerivedCategory := Iso.refl _
  exact Functor.whiskerRight adj.unit U.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (derivedScalars a X)
      ((Functor.mapDerivedCategoryCompIso R U) ≪≫ r).hom

/-- The scalar adjunction unit transported through the specified realizations.
Every component is constructed independently of a quotient model or limit cone.
Source: coefficient changes (1), derived scalar adjunction
(blueprint: def-diagonal-cyclic-quotient-augmentation). -/
def cyclicEvaluationAugmentation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    cyclicDiscreteRestriction l (diagonalSurface Y) ⋙
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory ⟶
      cyclicEvaluationFunctor l Y n eW p ⋙
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory :=
  (cyclicCompletedUnderlying l Y eW).hom ≫
    Functor.whiskerLeft eW.F.mapDerivedCategory
      (scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y)) ≫
    (cyclicEvaluationUnderlying l Y n eW p).inv

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
