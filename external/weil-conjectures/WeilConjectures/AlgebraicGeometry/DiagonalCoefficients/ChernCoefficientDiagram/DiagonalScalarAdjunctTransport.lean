/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerAdjunctConditions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarUnitPush

/-! # Transport through the two scalar changes

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

private theorem transport_unit_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ C') (G : D ⥤ D') (R : D ⥤ C) (R' : D' ⥤ C')
    (t : R ⋙ F ⟶ G ⋙ R')
    {U : C} {V W : D} {U' : C'} {V' W' : D'}
    (a : U ⟶ R.obj V) (a' : U' ⟶ R'.obj V')
    (u : F.obj U ⟶ U') (i : G.obj V ≅ V') (z : V ⟶ W) (v : G.obj W ⟶ W')
    (h : F.map a ≫ t.app V ≫ R'.map i.hom = u ≫ a') :
    F.map (a ≫ R.map z) ≫ (t.app W ≫ R'.map v) =
      u ≫ (a' ≫ R'.map ((i.inv ≫ G.map z) ≫ v)) := by
  have hn := t.naturality z
  change F.map (R.map z) ≫ t.app W = t.app V ≫ R'.map (G.map z) at hn
  have hz : G.map z ≫ v = i.hom ≫ ((i.inv ≫ G.map z) ≫ v) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = F.map a ≫ t.app V ≫ R'.map (G.map z ≫ v) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hn]
    _ = (F.map a ≫ t.app V ≫ R'.map i.hom) ≫
        R'.map ((i.inv ≫ G.map z) ≫ v) := by
      rw [hz, R'.map_comp]
      simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Category.assoc]

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

section AbstractDiagram
variable {B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
  {A : Type (u + 1)} [CommRing A] [Finite A]
  {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {hY : IsUnit (N : Γ(Y, ⊤))}

/-- The completed local arrow after the two scalar changes.
Source: coefficient changes (1).
(blueprint: lem-diagonal-scalar-adjunct-transport). -/
@[irreducible]
def ChernCoefficientDiagram.scalarLocalArrow
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    unit R (ProjectiveLine Y) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (x.L (ProjectiveLine Y)))⟦(2 : ℤ)⟧ :=
  let G₀ := x.completedP.F.mapDerivedCategory
  let G₁ := derivedScalars x.b (ProjectiveLine Y)
  let G₂ := derivedScalars x.q (ProjectiveLine Y)
  let i₀ := (x.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso x.completedP.unitIso
  let z₀ := (i₀.inv ≫ G₀.map z) ≫ x.completedP.shiftedLine l (ProjectiveLine Y)
  let z₁ := ((x.toIntegral.units (ProjectiveLine Y)).iso.inv ≫ G₁.map z₀) ≫
    x.toIntegral.lineP.shift x.b
  ((x.scalar.units (ProjectiveLine Y)).iso.inv ≫ G₂.map z₁) ≫ x.scalar.lineP.shift x.q

/-- Transport through completion and the two scalar changes, before finite realization.
Source: coefficient changes (1).
(blueprint: lem-diagonal-scalar-adjunct-transport). -/
@[irreducible]
def ChernCoefficientDiagram.ScalarTransportTo
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    (c : DiagonalTrace.completedUnit l Y ⟶
      x.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    (w : unit R Y ⟶ x.d.Rq.R.obj
      (((DerivedCategory.singleFunctor _ 0).obj (x.L (ProjectiveLine Y)))⟦(2 : ℤ)⟧)) : Prop :=
  let F₀ := x.completedY.F.mapDerivedCategory
  let F₁ := derivedScalars x.b Y
  let F₂ := derivedScalars x.q Y
  let u₀ := x.completedY.singleUnit l Y
  let u₁ := (x.toIntegral.units Y).iso.hom
  let u₂ := (x.scalar.units Y).iso.hom
  let v₀ := x.q_square.derived.iso.hom.app _ ≫
    x.zl.Rq.R.map (x.completedP.shiftedLine l (ProjectiveLine Y))
  let v₁ := (x.toIntegral.q.square.mate x.b).app _ ≫
    x.integral.Rq.R.map (x.toIntegral.lineP.shift x.b)
  let v₂ := (x.scalar.q.square.mate x.q).app _ ≫
    x.d.Rq.R.map (x.scalar.lineP.shift x.q)
  (F₀ ⋙ F₁ ⋙ F₂).map c ≫ (F₂.map (F₁.map v₀ ≫ v₁) ≫ v₂) =
    (F₂.map (F₁.map u₀ ≫ u₁) ≫ u₂) ≫ w

/-- The two scalar-unit squares transport any completed first square.
Source: coefficient changes (1), scalar adjunction and mate naturality.
(blueprint: lem-diagonal-scalar-adjunct-transport).
Proof: scalar_unit_push gives the unit square for each coefficient map.
Naturality of each mate transports an arbitrary local arrow. Compose both squares
with the supplied first square and identify the nested local arrow. -/
theorem scalar_adjunct_transport
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
    x.ScalarTransportTo l Y c
      (coefficientUnitPush R Y x.d.Rq ≫ x.d.Rq.R.map (x.scalarLocalArrow l Y z)) := by
  let F₀ := x.completedY.F.mapDerivedCategory
  let F₁ := derivedScalars x.b Y
  let F₂ := derivedScalars x.q Y
  let G₀ := x.completedP.F.mapDerivedCategory
  let G₁ := derivedScalars x.b (ProjectiveLine Y)
  let G₂ := derivedScalars x.q (ProjectiveLine Y)
  let R₁ := x.zl.Rq.R
  let R₂ := x.integral.Rq.R
  let R₃ := x.d.Rq.R
  let i₀ := (x.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso x.completedP.unitIso
  let i₁ := (x.toIntegral.units (ProjectiveLine Y)).iso
  let i₂ := (x.scalar.units (ProjectiveLine Y)).iso
  let j₀ := x.completedP.shiftedLine l (ProjectiveLine Y)
  let j₁ := x.toIntegral.lineP.shift x.b
  let j₂ := x.scalar.lineP.shift x.q
  let z₀ := (i₀.inv ≫ G₀.map z) ≫ j₀
  let z₁ := (i₁.inv ≫ G₁.map z₀) ≫ j₁
  let z₂ := (i₂.inv ≫ G₂.map z₁) ≫ j₂
  let a₁ := coefficientUnitPush _ Y x.zl.Rq
  let a₂ := coefficientUnitPush _ Y x.integral.Rq
  let a₃ := coefficientUnitPush _ Y x.d.Rq
  let t₁ := x.toIntegral.q.square.mate x.b
  let t₂ := x.scalar.q.square.mate x.q
  have h₁ := transport_unit_adjunct F₁ G₁ R₁ R₂ t₁ a₁ a₂
    (x.toIntegral.units Y).iso.hom i₁ z₀ j₁
    (scalar_unit_push x.b Y x.zl.Rq x.integral.Rq x.toIntegral.q.square
      (x.toIntegral.units Y) (x.toIntegral.units (ProjectiveLine Y)))
  have h₂ := transport_unit_adjunct F₂ G₂ R₂ R₃ t₂ a₂ a₃
    (x.scalar.units Y).iso.hom i₂ z₁ j₂
    (scalar_unit_push x.q Y x.integral.Rq x.d.Rq x.scalar.q.square
      (x.scalar.units Y) (x.scalar.units (ProjectiveLine Y)))
  have ht := compose_arrow_square F₂ (compose_arrow_square F₁ first h₁) h₂
  unfold ChernCoefficientDiagram.ScalarTransportTo
  simpa only [ChernCoefficientDiagram.scalarLocalArrow, F₀, F₁, F₂, G₀, G₁, G₂,
    R₁, R₂, R₃, i₀, i₁, i₂, j₀, j₁, j₂, z₀, z₁, z₂, a₁, a₃, t₁, t₂,
    Functor.comp_map] using ht

end AbstractDiagram
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
