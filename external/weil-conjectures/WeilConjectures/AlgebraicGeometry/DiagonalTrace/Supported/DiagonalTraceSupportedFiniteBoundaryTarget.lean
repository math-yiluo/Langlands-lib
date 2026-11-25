/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryMaps
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceConcreteClassIdentification
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteSupportedComparison

/-! # The finite Chern equation for a normalized strict supported Cartier class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap
  Ext.comp Ext.mk₀ Ext.mapExactFunctor Ext.homEquiv

private theorem coordinate_composite_eq
    {C : Type*} [Category C] {X Y P Q R : C}
    (e : X ≅ P) (d : Y ≅ Q)
    (g : P ⟶ R) (z : R ⟶ Q) (f : X ⟶ Y) (t : P ⟶ Q)
    (h₁ : g ≫ z = t) (h₂ : t = e.inv ≫ f ≫ d.hom) :
    e.hom ≫ g ≫ z ≫ d.inv = f := by
  have h := h₁.trans h₂
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem finite_supported_coordinate_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) (z : GeoCartierClass A N hA i)
    (v : Ext (Etale.ordinaryFiniteConstant A T)
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hz : (Ext.mk₀
      (((comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A))).comp z (zero_add 2) =
      v.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) T))
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasExt.{u + 1} E] [HasDerivedCategory C] [HasDerivedCategory E]
    [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
    (F : C ⥤ (ℕᵒᵖ ⥤ E))
    (S : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ E)
    [F.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {X Y : C} (n : ℕ)
    (a : (F.obj X).obj (op n) ≅ S.obj (geoCartierConstant A T))
    (b : (F.obj Y).obj (op n) ≅ S.obj (geoCartierLine A N hA T))
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (hb : finiteEvaluationEquation F S n a b f (finiteEtaleProImage A T N hA v))
    :
    (supportedFiniteSingleCoordinates F X n a).hom ≫
      (DerivedCategory.singleFunctor E 0).map
        (S.map (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A))) ≫ (z.mapExactFunctor S).hom ≫
      (supportedFiniteShiftedCoordinates F Y n b).inv =
    (((evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategory).map
      (F.mapDerivedCategory.map f) := by
  unfold finiteEvaluationEquation at hb
  exact coordinate_composite_eq _ _ _ _ _ _
    (finiteSupportedComparison_hom A N hA i z v hz S) hb

set_option linter.unusedVariables false in
/-- A finite class satisfying the geometric Kummer Chern equation gives the
normalized coefficient Chern arrow. This contains no strict class, source cone,
or presentation. It applies to any finite Cartier class with the stated equation.

Source: diagonal trace proof (2), coefficient comparison; classes proof (3).
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-target-step).

Proof: construct an étale lift of the finite evaluated Chern arrow using exact
residue reduction. FiniteChernNormalization identifies the integral class of
this lift with the positive Kummer class of diagonalPic. Ordinary finite Chern
uniqueness identifies it with the étale antecedent supplied by hz, whose
integral adjunct is supportedKummerChern. The diagonal Picard line is the dual
diagonal ideal. Cancel the constant comparison in the other equation of hz,
apply exact scalar restriction, and take Ext hom. This identifies the middle
arrow in the frame. Both composites have the same coefficient projection
prefix; cancellation of the frame isomorphisms proves the result.
The normalization hn is not needed after the finite comparison hc is supplied.
The argument works at positive exponent n+1, including n=0 and the empty scheme. -/
theorem diagonalTrace_supportedFiniteBoundary_targetStep
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hn : c.Normalized l (ULift.{u} (Padic l)))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (z : GeoCartierClass (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y))
    (hz : GeoCartierChernEquation (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)
      (diagonalImmersion_cartier Y) (diagonalSurface_power_unit l Y hY n) z) :
    a.cartierMap l Y hY c r k n L z =
      finiteChernComposite l (diagonalSurface Y) c r k L n
        (SpTowerClasses.diagonalPic Y) := by
  clear hn
  obtain ⟨c₁, hb, hz₁⟩ :=
    diagonalTrace_concreteClass_identification l Y hY c hc r k n a z hz
  delta SupportedFiniteBoundaryFrame.cartierMap finiteChernComposite
    diagonalExactFunctorExtImage
  apply congrArg (fun q =>
    (k.unitMap l (ULift.{u} (Padic l)) L ≫ (L.projection n).app _) ≫ q)
  exact finite_supported_coordinate_eq (diagonalResidue.{u} l n)
    (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) (diagonalImmersion Y) z c₁ hz₁
    r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n a.coefficient a.line
    (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c (SpTowerClasses.diagonalPic Y)) hb

end AlgebraicGeometry.ProEtale.DiagonalTrace
