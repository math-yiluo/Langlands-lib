/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteTracePresentation.DiagonalFiniteTraceChernCriterion
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift

/-! # Explicit coefficient transport for the completed Chern adjunct

Source: diagonal tower coefficient changes proof (1), and trace proof (1).
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
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

/-- The Chern-arrow equation through four successive coefficient functors.
All composites use only the supplied functors and endpoint maps.
Source: diagonal tower coefficient changes proof (1).
(blueprint: def-diagonal-uniformizer-chern-transport). -/
@[irreducible]
def fourStepChernCommutes
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    (F₀ : C₀ ⥤ C₁) (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄)
    {U₀ V₀ : C₀} {U₁ V₁ : C₁} {U₂ V₂ : C₂} {U₃ V₃ : C₃} {U₄ V₄ : C₄}
    (u₀ : F₀.obj U₀ ⟶ U₁) (v₀ : F₀.obj V₀ ⟶ V₁)
    (u₁ : F₁.obj U₁ ⟶ U₂) (v₁ : F₁.obj V₁ ⟶ V₂)
    (u₂ : F₂.obj U₂ ⟶ U₃) (v₂ : F₂.obj V₂ ⟶ V₃)
    (u₃ : F₃.obj U₃ ⟶ U₄) (v₃ : F₃.obj V₃ ⟶ V₄)
    (c : U₀ ⟶ V₀) (c' : U₄ ⟶ V₄) : Prop :=
  (F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃).map c ≫
      (F₃.map (F₂.map (F₁.map v₀ ≫ v₁) ≫ v₂) ≫ v₃) =
    (F₃.map (F₂.map (F₁.map u₀ ≫ u₁) ≫ u₂) ≫ u₃) ≫ c'

private theorem compose_trace_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} {A'' B'' : D}
    {t : A ⟶ B} {u : B ⟶ B'} {v : A ⟶ A'} {t' : A' ⟶ B'}
    {u' : F.obj B' ⟶ B''} {v' : F.obj A' ⟶ A''} {t'' : A'' ⟶ B''}
    (h : t ≫ u = v ≫ t') (h' : F.map t' ≫ u' = v' ≫ t'') :
    F.map t ≫ (F.map u ≫ u') = (F.map v ≫ v') ≫ t'' := by
  rw [← F.map_comp_assoc, h, F.map_comp]
  simp only [Category.assoc, h']

/-- Four trace squares transport a Chern/trace identity to the last category.
Source: diagonal tower coefficient changes proof (1), composition of trace squares.
(blueprint: def-diagonal-uniformizer-chern-transport). -/
theorem fourStepChernDegree
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    (F₀ : C₀ ⥤ C₁) (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄)
    {U₀ V₀ : C₀} {U₁ V₁ : C₁} {U₂ V₂ : C₂} {U₃ V₃ : C₃} {U₄ V₄ : C₄}
    (u₀ : F₀.obj U₀ ⟶ U₁) (v₀ : F₀.obj V₀ ⟶ V₁)
    (u₁ : F₁.obj U₁ ⟶ U₂) (v₁ : F₁.obj V₁ ⟶ V₂)
    (u₂ : F₂.obj U₂ ⟶ U₃) (v₂ : F₂.obj V₂ ⟶ V₃)
    (u₃ : F₃.obj U₃ ⟶ U₄) (v₃ : F₃.obj V₃ ⟶ V₄)
    (c : U₀ ⟶ V₀) (c' : U₄ ⟶ V₄)
    [IsIso u₀] [IsIso u₁] [IsIso u₂] [IsIso u₃]
    (t₀ : V₀ ⟶ U₀) (t₁ : V₁ ⟶ U₁) (t₂ : V₂ ⟶ U₂)
    (t₃ : V₃ ⟶ U₃) (t₄ : V₄ ⟶ U₄)
    (h₀ : F₀.map t₀ ≫ u₀ = v₀ ≫ t₁)
    (h₁ : F₁.map t₁ ≫ u₁ = v₁ ≫ t₂)
    (h₂ : F₂.map t₂ ≫ u₂ = v₂ ≫ t₃)
    (h₃ : F₃.map t₃ ≫ u₃ = v₃ ≫ t₄)
    (hct : c ≫ t₀ = 𝟙 _)
    (hc : fourStepChernCommutes F₀ F₁ F₂ F₃ u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ c c') :
    c' ≫ t₄ = 𝟙 _ := by
  let F := F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃
  let u := F₃.map (F₂.map (F₁.map u₀ ≫ u₁) ≫ u₂) ≫ u₃
  let v := F₃.map (F₂.map (F₁.map v₀ ≫ v₁) ≫ v₂) ≫ v₃
  have ht := compose_trace_square F₁ h₀ h₁
  have ht := compose_trace_square F₂ ht h₂
  have ht := compose_trace_square F₃ ht h₃
  change F.map t₀ ≫ u = v ≫ t₄ at ht
  unfold fourStepChernCommutes at hc
  change F.map c ≫ v = u ≫ c' at hc
  have : IsIso u := by dsimp only [u]; infer_instance
  apply (cancel_epi u).mp
  calc
    _ = (F.map c ≫ v) ≫ t₄ := by rw [hc]; simp only [Category.assoc]
    _ = F.map c ≫ (F.map t₀ ≫ u) := by rw [Category.assoc, ← ht]
    _ = u := by rw [← Category.assoc, ← F.map_comp, hct, F.map_id, Category.id_comp]
    _ = _ := (Category.comp_id u).symm

/-- The coefficient diagrams needed by the formal Chern/trace calculation.
The coefficient rings are parameters, so the calculation never unfolds their constructions.
Source: diagonal tower coefficient changes proof (1).
(blueprint: def-diagonal-uniformizer-chern-transport). -/
structure ChernCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hY : IsUnit (N : Γ(Y, ⊤))) where
  zl : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l)
  LB : ∀ X : Scheme.{u}, Modules B X
  L : ∀ X : Scheme.{u}, Modules R X
  integral : Diagram B Y LB
  d : Diagram R Y L
  b : Profinite.continuousMapRingObj.{u} ℤ_[l] ⟶ B
  [b_mon : IsMonHom b]
  q : B ⟶ R
  [q_mon : IsMonHom q]
  mb : ∀ X : Scheme.{u}, (zlLine l X).X ⟶ (LB X).X
  mq : ∀ X : Scheme.{u}, (LB X).X ⟶ (L X).X
  toIntegral : ScalarCompatibility b Y (zlLine l) LB mb zl integral
  scalar : ScalarCompatibility q Y LB L mq integral d
  tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y)
  completedY : CompletedRealization l Y
  completedP : CompletedRealization l (ProjectiveLine Y)
  q_square : CompletedPushSquare l (ProjectiveLine Y ↘ Y)
    completedP completedY tq.Rc zl.Rq
  eY : FiniteRealization R A Y
  eP : FiniteRealization R A (ProjectiveLine Y)
  lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y)
  presentation : FiniteTracePresentation R A N hN hA Y hY L d eY eP
  c : DiagonalTrace.completedUnit l Y ⟶
    tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)

attribute [instance] ChernCoefficientDiagram.b_mon ChernCoefficientDiagram.q_mon

section AbstractCoefficients
variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]
  {B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
  {A : Type (u + 1)} [CommRing A] [Finite A]
  {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {hY : IsUnit (N : Γ(Y, ⊤))}

/-- The Chern equation for an abstract coefficient diagram, before composing traces.
Source: diagonal tower coefficient changes proof (1).
(blueprint: def-diagonal-uniformizer-chern-transport). -/
@[irreducible]
def ChernCoefficientDiagram.Commutes
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY) : Prop :=
  let F₀ := x.completedY.F.mapDerivedCategory
  let F₁ := derivedScalars x.b Y
  let F₂ := derivedScalars x.q Y
  let F₃ := x.eY.F.mapDerivedCategory
  let u₀ := x.completedY.singleUnit l Y
  let u₁ := (x.toIntegral.units Y).iso.hom
  let u₂ := (x.scalar.units Y).iso.hom
  let u₃ := x.eY.derivedUnit
  let v₀ := x.q_square.derived.iso.hom.app
      ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) ≫
    x.zl.Rq.R.map (x.completedP.shiftedLine l (ProjectiveLine Y))
  let v₁ := (x.toIntegral.q.square.mate x.b).app _ ≫
    x.integral.Rq.R.map (x.toIntegral.lineP.shift x.b)
  let v₂ := (x.scalar.q.square.mate x.q).app _ ≫
    x.d.Rq.R.map (x.scalar.lineP.shift x.q)
  let v₃ := (x.presentation.comparison
    R
    A
    N hN hA Y hY
    x.L x.d x.eY x.eP x.lineP).hom
  fourStepChernCommutes F₀ F₁ F₂ F₃ u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ x.c
    (biprod.inr ≫ geoP1TwistedMap A N hN hA Y hY)

attribute [local semireducible] ChernCoefficientDiagram.Commutes
  FiniteTracePresentation.realizedTrace

/-- The prescribed scalar trace squares transport degree one to finite coefficients.
Source: diagonal tower coefficient changes proof (1), composition of trace squares.
(blueprint: def-diagonal-uniformizer-chern-transport). -/
theorem ChernCoefficientDiagram.traceDegree
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    (hc : x.Commutes) (hct : x.c ≫ x.tq.trace = 𝟙 _)
    (q_trace : CompletedTraceCompatibility l (ProjectiveLine Y ↘ Y)
      x.completedP x.completedY x.tq x.zl.Rq x.q_square x.zl.traceq) :
    FiniteTraceChernDegree R A N hN hA Y hY x.L x.d x.eY x.eP x.lineP x.presentation := by
  let F₀ := x.completedY.F.mapDerivedCategory
  let F₁ := derivedScalars x.b Y
  let F₂ := derivedScalars x.q Y
  let F₃ := x.eY.F.mapDerivedCategory
  let u₀ := x.completedY.singleUnit l Y
  let u₁ := (x.toIntegral.units Y).iso.hom
  let u₂ := (x.scalar.units Y).iso.hom
  let u₃ := x.eY.derivedUnit
  let v₀ := x.q_square.derived.iso.hom.app
      ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) ≫
    x.zl.Rq.R.map (x.completedP.shiftedLine l (ProjectiveLine Y))
  let v₁ := (x.toIntegral.q.square.mate x.b).app _ ≫
    x.integral.Rq.R.map (x.toIntegral.lineP.shift x.b)
  let v₂ := (x.scalar.q.square.mate x.q).app _ ≫
    x.d.Rq.R.map (x.scalar.lineP.shift x.q)
  let v₃ := (x.presentation.comparison
    R
    A
    N hN hA Y hY
    x.L x.d x.eY x.eP x.lineP).hom
  let t := x.presentation.realizedTrace
    R
    A
    N hN hA Y hY
    x.L x.d x.eY x.eP x.lineP
  have h₀ : F₀.map x.tq.trace ≫ u₀ = v₀ ≫ x.zl.traceq := by
    exact q_trace.trans (Category.assoc _ _ _).symm
  have h₁ : F₁.map x.zl.traceq ≫ u₁ = v₁ ≫ x.integral.traceq := by
    exact x.toIntegral.q.trace.trans (Category.assoc _ _ _).symm
  have h₂ : F₂.map x.integral.traceq ≫ u₂ = v₂ ≫ x.d.traceq := by
    simpa only [F₂, u₂, v₂, Category.assoc] using x.scalar.q.trace
  have h₃ : F₃.map x.d.traceq ≫ u₃ = v₃ ≫ t := by
    let e := x.presentation.comparison
      R
      A
      N hN hA Y hY
      x.L x.d x.eY x.eP x.lineP
    change F₃.map x.d.traceq ≫ u₃ = e.hom ≫ (e.inv ≫ F₃.map x.d.traceq ≫ u₃)
    exact (e.hom_inv_id_assoc (F₃.map x.d.traceq ≫ u₃)).symm
  have : IsIso u₀ := by
    dsimp only [u₀]
    unfold CompletedRealization.singleUnit
    infer_instance
  have : IsIso u₃ := by
    dsimp only [u₃]
    unfold FiniteRealization.derivedUnit
    infer_instance
  unfold FiniteTraceChernDegree
  change biprod.inr ≫
    geoP1TwistedMap A
      N hN hA Y hY ≫ t = 𝟙 _
  rw [← Category.assoc]
  exact fourStepChernDegree F₀ F₁ F₂ F₃ u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ x.c _
    x.tq.trace x.zl.traceq x.integral.traceq x.d.traceq t h₀ h₁ h₂ h₃ hct hc

end AbstractCoefficients

/-- The actual inputs to the positive Chern coefficient comparison.
Every field is supplied data or a normalization already assumed in that comparison;
no Chern-arrow equation or trace-degree equation is included.
Source: diagonal tower coefficient changes proof (1).
(blueprint: def-diagonal-uniformizer-chern-transport). -/
structure UniformizerChernNormalizationData
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)] where
  zl : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l)
  E : PadicAlgCl.FiniteIntermediateField l
  π : PadicAlgCl.integers l E
  hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)
  n : ℕ
  integral : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
    (fun X ↦ spIntegralTwist X l E)
  toIntegral : ScalarCompatibility (integralMap l E) Y (zlLine l)
    (fun X ↦ spIntegralTwist X l E) (integralLineMap l E) zl integral
  tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y)
  completedY : CompletedRealization l Y
  completedP : CompletedRealization l (ProjectiveLine Y)
  q_model : tq.model.model = Iso.refl (ProjectiveLine Y)
  q_square : CompletedPushSquare l (ProjectiveLine Y ↘ Y)
    completedP completedY tq.Rc zl.Rq
  [hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))]
  hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0
  hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤))
  d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    Y (quotientLine l E π n)
  scalar : ScalarCompatibility (quotientMap l E π n) Y
    (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
    (quotientLineMap l E π n) integral d
  eY : FiniteRealization
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (ULift.{u + 1} (completedResidue l E π n)) Y
  eP : FiniteRealization
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y)
  lineP : QuotientLineRealization l E π n n hA (ProjectiveLine Y) eP
  presentation : FiniteTracePresentation
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (ULift.{u + 1} (completedResidue l E π n))
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow
    (quotientLine l E π n) d eY eP
  c : DiagonalTrace.completedUnit l Y ⟶
    tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
  hc : (diagonalCompletedUnderlying l Y).map c ≫
      tq.toPresentation.sourceMap l (ULift.{u} (Padic l)) =
    tq.coefficientsS.unitMap l (ULift.{u} (Padic l)) tq.LS ≫
      tq.LS.R.map (tq.toPresentation.systemChern l)

attribute [instance] UniformizerChernNormalizationData.hfinite

/-- The formal coefficient diagram supplied by the actual uniformizer data.
Source: diagonal tower coefficient changes proof (1).
(blueprint: def-diagonal-uniformizer-chern-transport). -/
def UniformizerChernNormalizationData.diagram
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y) :
    ChernCoefficientDiagram l Y (Profinite.padicIntegersRingObj.{u} l s.E.1)
      (Profinite.continuousMapRingObj.{u} (completedResidue l s.E s.π s.n))
      (ULift.{u + 1} (completedResidue l s.E s.π s.n))
      (l ^ (s.n + 1)) (pow_pos (Fact.out : l.Prime).pos _) s.hA s.hYpow :=
  { zl := s.zl
    LB := fun X ↦ spIntegralTwist X l s.E
    L := quotientLine l s.E s.π s.n
    integral := s.integral
    d := s.d
    b := integralMap l s.E
    q := quotientMap l s.E s.π s.n
    mb := integralLineMap l s.E
    mq := quotientLineMap l s.E s.π s.n
    toIntegral := s.toIntegral
    scalar := s.scalar
    tq := s.tq
    completedY := s.completedY
    completedP := s.completedP
    q_square := s.q_square
    eY := s.eY
    eP := s.eP
    lineP := s.lineP.iso l
    presentation := s.presentation
    c := s.c }

/-- The positive Chern comparison for the specified four coefficient changes.
This is the explicit Chern-arrow equation, before composing any trace.
Source: diagonal tower coefficient changes proof (1).
(blueprint: def-diagonal-uniformizer-chern-transport). -/
@[irreducible]
def UniformizerChernNormalizationData.ChernNormalized
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y) : Prop :=
  (s.diagram l Y).Commutes

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
