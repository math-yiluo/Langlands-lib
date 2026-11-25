/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretrace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift

/-! # Explicit scalar transport of the two positive Chern adjuncts

The input Chern arrows are supplied with their whole-system normalization. No arrow
is chosen by a mere existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] diagram derivedScalars
attribute [local irreducible] moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square

/-- The whole-system equation determining a completed Chern adjunct. -/
def CompletedChernNormalized (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (a : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧)) : Prop :=
  (diagonalCompletedUnderlying l S).map a ≫ p.sourceMap l (ULift.{u} (Padic l)) =
    p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
      p.LS.R.map (p.systemChern l)

/-- Realize a completed positive Chern adjunct, using the prescribed unit and line maps. -/
@[irreducible]
def realizeScalarChern (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (R' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (s : CompletedPushSquare l f eX eS R R')
    (c : DiagonalTrace.completedUnit l S ⟶
      R.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧)) :
    unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S ⟶
      R'.R.obj (((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
          (zlLine l X)) ⟦(2 : ℤ)⟧) :=
  letI : IsIso (eS.singleUnit l S) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  inv (eS.singleUnit l S) ≫ eS.F.mapDerivedCategory.map c ≫
    s.derived.iso.hom.app _ ≫ R'.R.map (eX.shiftedLine l X)

/-- Extend one actual Chern arrow through a specified scalar/direct-image mate. -/
@[irreducible]
def extendScalarChern
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (cU : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (cL : Endpoint a M M' m)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (s : RestrictionSquare a f R R')
    (c : unit Λ S ⟶ R.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧)) :
    unit Λ' S ⟶ R'.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj M') ⟦(2 : ℤ)⟧) :=
  cU.iso.inv ≫ (derivedScalars a S).map c ≫
    (s.mate a).app _ ≫ R'.R.map (cL.shift a)

/-- The scalar extension of the q Chern adjunct, then its canonical pushforward comparison. -/
@[irreducible]
def scalarQChern (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) (Y : Scheme.{u})
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    {δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y}
    {family : Family l Y} (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)) :
    unit (coefficient l c).X Y ⟶
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) := by
  let z := realizeScalarChern l _ r.eP r.eY r.tq.Rc family.zl.Rq r.q_square a
  let i (E : PadicAlgCl.FiniteIntermediateField l) :=
    extendScalarChern (integralMap l E) _ ((family.toIntegral E).units Y)
      (family.toIntegral E).lineP family.zl.Rq (family.integral E).Rq
      (family.toIntegral E).q.square z
  let q (E : PadicAlgCl.FiniteIntermediateField l) :=
    extendScalarChern (padicIntegersRingObjToContinuousMapRingObj l E) _
      ((family.toRational E).units Y) (family.toRational E).lineP
      (family.integral E).Rq (family.rational E).Rq (family.toRational E).q.square (i E)
  cases c with
  | some E =>
    exact q E ≫ (eqToIso (family.rational E).q_canonical).hom.app _
  | none =>
    let E := bottomField l
    exact extendScalarChern (Profinite.padicSubfieldRingObjToPadicAlgCl l E) _
      ((family.toClosure E).units Y) (family.toClosure E).lineP
      (family.rational E).Rq family.closure.Rq (family.toClosure E).q.square (q E) ≫
        (eqToIso family.closure.q_canonical).hom.app _

/-- The independent p2 Chern adjunct, extended through its own scalar mates. -/
@[irreducible]
def scalarP2Chern (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) (Y : Scheme.{u})
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    {δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y}
    {family : Family l Y} (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧)) :
    unit (coefficient l c).X (ProjectiveLine Y) ⟶
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) := by
  let z := realizeScalarChern l _ r.eW r.eP r.t₂.Rc family.zl.R₂ r.p₂_square a
  let i (E : PadicAlgCl.FiniteIntermediateField l) :=
    extendScalarChern (integralMap l E) _ ((family.toIntegral E).units (ProjectiveLine Y))
      (family.toIntegral E).lineW family.zl.R₂ (family.integral E).R₂
      (family.toIntegral E).p₂.square z
  let q (E : PadicAlgCl.FiniteIntermediateField l) :=
    extendScalarChern (padicIntegersRingObjToContinuousMapRingObj l E) _
      ((family.toRational E).units (ProjectiveLine Y)) (family.toRational E).lineW
      (family.integral E).R₂ (family.rational E).R₂ (family.toRational E).p₂.square (i E)
  cases c with
  | some E =>
    exact q E ≫ (secondDiagramPushIso _ Y _ (family.rational E)).hom.app _
  | none =>
    let E := bottomField l
    exact extendScalarChern (Profinite.padicSubfieldRingObjToPadicAlgCl l E) _
      ((family.toClosure E).units (ProjectiveLine Y)) (family.toClosure E).lineW
      (family.rational E).R₂ family.closure.R₂ (family.toClosure E).p₂.square (q E) ≫
        (secondDiagramPushIso _ Y _ family.closure).hom.app _

/-- The unit comparison with degree-zero coefficient units as endpoints. -/
@[irreducible]
def scalarUnitPullIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj (unit Λ Y) ≅
      unit Λ (ProjectiveLine Y) :=
  (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).mapIso (singleUnitIso Λ Y) ≪≫
    secondTraceUnitIso Λ Y ≪≫ (singleUnitIso Λ (ProjectiveLine Y)).symm

/-- The shifted root-normalized line comparison along q. -/
@[irreducible]
def scalarQLineIso (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X Y) 0).obj
        (line l c Y)) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
        (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧ := by
  letI : ∀ x : Y, Invertible (l : Y.residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _ (Y ↘ Spec (.of k)) x).invertible
  letI : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  exact shiftedLineComparison l c (ProjectiveLine Y ↘ Y)

/-- The twisted unit adjunct of a specified shifted-line comparison. -/
@[irreducible]
def scalarTwistedUnit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (T : DerivedCategory (Modules Λ S)) (T' : DerivedCategory (Modules Λ X))
    (e : (moduleObjectDerivedPullback Λ f).obj T ≅ T') :
    T ⟶ (moduleObjectDerivedPushforward Λ f).obj T' := by
  refine ?_ ≫ (moduleObjectDerivedPushforward Λ f).map e.hom
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).unit.app T

end AlgebraicGeometry.ProEtale.RationalP1
