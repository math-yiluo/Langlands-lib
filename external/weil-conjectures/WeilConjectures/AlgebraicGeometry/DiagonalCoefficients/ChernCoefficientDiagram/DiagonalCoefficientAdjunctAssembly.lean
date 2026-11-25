/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ChernCoefficientDiagram.DiagonalScalarAdjunctTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalFiniteUnitArrowTransport

/-! # Assembly of the four coefficient adjunct squares

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Endpoint.shift Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem compose_arrow_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V U' V' : C} {U'' V'' : D}
    {c : U ⟶ V} {c' : U' ⟶ V'} {c'' : U'' ⟶ V''}
    {u : U ⟶ U'} {v : V ⟶ V'}
    {u' : F.obj U' ⟶ U''} {v' : F.obj V' ⟶ V''}
    (h : c ≫ v = u ≫ c') (h' : F.map c' ≫ v' = u' ≫ c'') :
    F.map c ≫ (F.map v ≫ v') = (F.map u ≫ u') ≫ c'' := by
  rw [← F.map_comp_assoc, h, F.map_comp]
  simp only [Category.assoc, h']

private theorem compose_last_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V U' V' : C} {U'' V'' : D}
    {c : U ⟶ V} {c' : U' ⟶ V'} {c'' w : U'' ⟶ V''}
    {u : U ⟶ U'} {v : V ⟶ V'}
    {u' : F.obj U' ⟶ U''} {v' v'' : F.obj V' ⟶ V''}
    (h : c ≫ v = u ≫ c') (h' : F.map c' ≫ v' = u' ≫ c'')
    (hv : v' = v'') (hw : c'' = w) :
    F.map c ≫ (F.map v ≫ v'') = (F.map u ≫ u') ≫ w := by
  subst v''
  subst w
  exact compose_arrow_square F h h'

private theorem nested_transport
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (G₀ : C₀ ⥤ C₁) (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) (G₃ : C₃ ⥤ C₄)
    {U₀ V₀ : C₀} {U₁ V₁ : C₁} {U₂ V₂ : C₂} {U₃ V₃ : C₃} {U₄ V₄ : C₄}
    (i₀ : G₀.obj U₀ ≅ U₁) (i₁ : G₁.obj U₁ ≅ U₂)
    (i₂ : G₂.obj U₂ ≅ U₃) (i₃ : G₃.obj U₃ ≅ U₄)
    (j₀ : G₀.obj V₀ ⟶ V₁) (j₁ : G₁.obj V₁ ⟶ V₂)
    (j₂ : G₂.obj V₂ ⟶ V₃) (j₃ : G₃.obj V₃ ⟶ V₄) (z : U₀ ⟶ V₀) :
    (i₃.inv ≫ G₃.map ((i₂.inv ≫ G₂.map
      ((i₁.inv ≫ G₁.map ((i₀.inv ≫ G₀.map z) ≫ j₀)) ≫ j₁)) ≫ j₂)) ≫ j₃ =
    (G₃.mapIso (G₂.mapIso (G₁.mapIso i₀ ≪≫ i₁) ≪≫ i₂) ≪≫ i₃).inv ≫
      (G₀ ⋙ G₁ ⋙ G₂ ⋙ G₃).map z ≫
        (G₃.map (G₂.map (G₁.map j₀ ≫ j₁) ≫ j₂) ≫ j₃) := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.comp_map,
    Functor.map_comp, Category.assoc]

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

section AbstractDiagram
variable {B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
  {A : Type (u + 1)} [CommRing A] [Finite A]
  {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {hY : IsUnit (N : Γ(Y, ⊤))}

/-- The local arrow through the four coefficient functors.
Source: coefficient changes (1).
(blueprint: lem-diagonal-coefficient-adjunct-assembly). -/
@[irreducible]
def ChernCoefficientDiagram.localAdjunctArrow
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    geoP1Unit A (ProjectiveLine Y) ⟶ geoP1Twist A N hA (ProjectiveLine Y) 1 2 :=
  (x.localUnitIso l Y).inv ≫
    (x.completedP.F.mapDerivedCategory ⋙ derivedScalars x.b (ProjectiveLine Y) ⋙
      derivedScalars x.q (ProjectiveLine Y) ⋙ x.eP.F.mapDerivedCategory).map z ≫
    (x.eP.F.mapDerivedCategory.map
      ((derivedScalars x.q (ProjectiveLine Y)).map
        ((derivedScalars x.b (ProjectiveLine Y)).map
          (x.completedP.shiftedLine l (ProjectiveLine Y)) ≫
            x.toIntegral.lineP.shift x.b) ≫ x.scalar.lineP.shift x.q) ≫
      x.eP.shiftedLine N hA (x.L (ProjectiveLine Y)) x.lineP)

/-- Four unit squares transport an arbitrary completed arrow and its adjunct.
Source: coefficient changes (1), functoriality and adjunction naturality.
(blueprint: lem-diagonal-coefficient-adjunct-assembly).
Proof: compose the first square with the two scalar-unit mate squares and the finite
unit square. Naturality transports the local arrow. The composite unit inverse
and line maps identify the local arrow, and adjunction naturality identifies its
finite adjunct. -/
theorem coefficient_adjunct_transport
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (c : DiagonalTrace.completedUnit l Y ⟶
      x.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    (first :
      let uP := (x.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso x.completedP.unitIso
      x.completedY.F.mapDerivedCategory.map c ≫
          (x.q_square.derived.iso.hom.app _ ≫
            x.zl.Rq.R.map (x.completedP.shiftedLine l (ProjectiveLine Y))) =
        x.completedY.singleUnit l Y ≫
          (coefficientUnitPush _ Y x.zl.Rq ≫ x.zl.Rq.R.map
            ((uP.inv ≫ x.completedP.F.mapDerivedCategory.map z) ≫
              x.completedP.shiftedLine l (ProjectiveLine Y)))) :
    x.TransportTo l Y c
      (finiteAdjunct A Y (ChernCoefficientDiagram.localAdjunctArrow l Y x z)) := by
  let F₀ := x.completedY.F.mapDerivedCategory
  let F₁ := derivedScalars (x.b) Y
  let F₂ := derivedScalars (x.q) Y
  let F₃ := x.eY.F.mapDerivedCategory
  let G₀ := x.completedP.F.mapDerivedCategory
  let G₁ := derivedScalars (x.b) (ProjectiveLine Y)
  let G₂ := derivedScalars (x.q) (ProjectiveLine Y)
  let G₃ := x.eP.F.mapDerivedCategory
  let R₁ := x.zl.Rq.R
  let R₂ := x.integral.Rq.R
  let R₃ := x.d.Rq.R
  let R₄ := geoP1Pushforward
    (A) (ProjectiveLine Y ↘ Y)
  let i₀ := (x.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso x.completedP.unitIso
  let i₁ := (x.toIntegral.units (ProjectiveLine Y)).iso
  let i₂ := (x.scalar.units (ProjectiveLine Y)).iso
  let i₃ := x.eP.unitIsoDerived
  let j₀ := x.completedP.shiftedLine l (ProjectiveLine Y)
  let j₁ := x.toIntegral.lineP.shift (x.b)
  let j₂ := x.scalar.lineP.shift (x.q)
  let j₃ := x.eP.shiftedLine N hA (x.L (ProjectiveLine Y)) x.lineP
  let z₀ := (i₀.inv ≫ G₀.map z) ≫ j₀
  let z₁ := (i₁.inv ≫ G₁.map z₀) ≫ j₁
  let z₂ := (i₂.inv ≫ G₂.map z₁) ≫ j₂
  let z₃ := (i₃.inv ≫ G₃.map z₂) ≫ j₃
  let a₃ := coefficientUnitPush _ Y x.d.Rq
  let t₁ := x.toIntegral.q.square.mate (x.b)
  let t₂ := x.scalar.q.square.mate (x.q)
  let t₃ := x.presentation.q_square.derived.iso.hom ≫
    Functor.whiskerLeft G₃ (eqToIso x.presentation.q_canonical).hom
  have hp := scalar_adjunct_transport l Y x z c first
  unfold ChernCoefficientDiagram.ScalarTransportTo at hp
  have hp' :
      F₂.map (F₁.map (F₀.map c)) ≫
          (F₂.map (F₁.map
            (x.q_square.derived.iso.hom.app _ ≫ R₁.map j₀) ≫
              (t₁.app _ ≫ R₂.map j₁)) ≫ (t₂.app _ ≫ R₃.map j₂)) =
        (F₂.map (F₁.map (x.completedY.singleUnit l Y) ≫
          (x.toIntegral.units Y).iso.hom) ≫ (x.scalar.units Y).iso.hom) ≫
            (a₃ ≫ R₃.map z₂) := by
    unfold ChernCoefficientDiagram.scalarLocalArrow at hp
    dsimp only [F₀, F₁, F₂, G₀, G₁, G₂,
      R₁, R₂, R₃, i₀, i₁, i₂, j₀, j₁, j₂, z₀, z₁, z₂, a₃, t₁, t₂,
      Functor.comp_map] at hp ⊢
    exact hp
  have h₃ := finite_unit_arrow_transport Y x.eY x.eP x.d.Rq x.presentation.Rq
    x.presentation.q_canonical x.presentation.hcanonical x.presentation.q_square z₂ j₃
  have hv₃ : t₃.app _ ≫ R₄.map j₃ =
      (x.presentation.comparison R A N hN hA Y hY
        x.L x.d x.eY x.eP x.lineP).hom := by
    simp only [t₃, NatTrans.comp_app, Functor.whiskerLeft_app,
      FiniteTracePresentation.comparison, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc]
    unfold FiniteRealization.shiftedLineIso
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
    change _ = x.presentation.q_square.derived.iso.hom.app _ ≫
      x.presentation.Rq.R.map
        (x.eP.shiftedLine _ _ _ x.lineP) ≫
      (eqToIso x.presentation.q_canonical).hom.app _
    rw [← (eqToIso x.presentation.q_canonical).hom.naturality]
  have hz₃ : z₃ = ChernCoefficientDiagram.localAdjunctArrow l Y x z := by
    have h := nested_transport G₀ G₁ G₂ G₃ i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ z
    dsimp only [z₃, z₂, z₁, z₀, i₀, i₁, i₂, i₃,
      G₀, G₁, G₂, G₃, j₀, j₁, j₂, j₃] at h ⊢
    unfold ChernCoefficientDiagram.localAdjunctArrow ChernCoefficientDiagram.localUnitIso
    unfold FiniteRealization.unitIsoDerived at h ⊢
    exact h
  have hc := congrArg (finiteAdjunct A Y) hz₃
  unfold ChernCoefficientDiagram.TransportTo
  unfold fourStepChernCommutes
  dsimp only [F₀, F₁, F₂, F₃, R₁, R₂, R₃, t₁, t₂, j₀, j₁, j₂, Functor.comp_map]
  exact compose_last_square F₃ hp' h₃ hv₃ hc

end AbstractDiagram

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
