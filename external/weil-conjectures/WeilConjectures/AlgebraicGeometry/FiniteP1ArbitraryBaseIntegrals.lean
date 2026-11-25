/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerNaturality
public import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
public import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalAlpha
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalChernComponents
import WeilConjectures.AlgebraicGeometry.FiniteP1KummerSplitting

/-!
# Finite projective-line splitting and diagonal integrals over arbitrary bases

proof.md, levelwise check
(auxiliary; not a blueprint node).

The splitting contains exactly its two normalized components. Its trace is the second
projection of its inverse. No Noetherian hypothesis or adjunction datum is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport projectiveLineTraceDatum
  projectiveLineDiagonalChart projectiveLineDiagonalProjection
  ordinaryFiniteUnitPullback ordinaryFiniteShiftedLinePullback
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward
  rightDerivedLowerStarComp rightDerivedLowerStarCongr

/-- The Kummer-normalized two-summand splitting at an arbitrary base. The Chern
specification is the actual scalar-extended Kummer class of the existing O(1).
Source: blueprint tower P1 adjunction, finite levelwise check
(auxiliary; not a blueprint node). -/
structure ArbitraryBaseFiniteP1Splitting (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) where
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  chern_spec : ordinaryFiniteP1ChernSpec A N hA S
    (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS) chern
  decomposition : ordinaryFiniteP1SplittingSource A N hA S ≅
    ordinaryFiniteP1SplittingTarget A N hA S
  decomposition_hom : decomposition.hom = ordinaryFiniteP1SplittingMap A N hA t S hS chern

/-- The trace is the second projection of the inverse of the normalized splitting.
Source: blueprint tower P1 adjunction, finite trace normalization
(auxiliary; not a blueprint node). -/
def ArbitraryBaseFiniteP1Splitting.trace {A : Type (u + 1)} [CommRing A] {N : ℕ}
    {hA : (N : A) = 0} {t : OrdinaryFiniteTwistTransport A N hA}
    {S : Scheme.{u}} {hS : IsUnit (N : Γ(S, ⊤))}
    (d : ArbitraryBaseFiniteP1Splitting A N hA t S hS) :
    ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S :=
  d.decomposition.inv ≫
    biprod.snd (X := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
      (Y := ordinaryFiniteUnit A S)

/-- The two arbitrary-base exchange squares, for the splitting and its trace.
All comparisons are the canonical arrows of the recorded dependency nodes.
Source: blueprint tower P1 adjunction, finite levelwise check and base-change normalization
(auxiliary; not a blueprint node). -/
def ArbitraryBaseFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))),
    let F := ordinaryFinitePullback A (X := S') (Y := S) f
    let G := ordinaryFinitePushforward A (X := ProjectiveLine S') (Y := S')
        (ProjectiveLine S' ↘ S')
    let e := ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      G.map (ordinaryFiniteShiftedLinePullback A N hA t
        (X := ProjectiveLine S') (Y := ProjectiveLine S)
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
        (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS)).hom
    let s := ordinaryFiniteP1DecompositionSourceMap A N hA t f hS
    (F.map (d S hS).decomposition.hom ≫ e = s ≫ (d S' hS').decomposition.hom) ∧
      (F.map (d S hS).trace ≫ (ordinaryFiniteUnitPullback A (X := S') (Y := S) f).hom =
        e ≫ (d S' hS').trace)

/-- Transport the specified trace on P1 over P along the canonical chart for either
projection of P times P. This uses the chart adjunction unit and derived composition,
followed by the normalized twist comparison and the given splitting's own trace.
Source: blueprint tower P1 adjunction, identification of the two projections with r_P
(auxiliary; not a blueprint node). -/
def arbitraryBaseFiniteP1DiagonalTrace (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫
    (d (ProjectiveLine S)
      (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS)).trace

attribute [local irreducible] ArbitraryBaseFiniteP1Splitting.trace
  ArbitraryBaseFiniteP1BaseChange arbitraryBaseFiniteP1DiagonalTrace

@[irreducible]
private def splittingFromMap
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS) c)
    (hi : IsIso (C := DerivedCategoryModule A S)
      (ordinaryFiniteP1SplittingMap A N hA t S hS c)) :
    ArbitraryBaseFiniteP1Splitting A N hA t S hS :=
  { chern := c
    chern_spec := hc
    decomposition := @asIso (DerivedCategoryModule A S) _
      (ordinaryFiniteP1SplittingSource A N hA S)
      (ordinaryFiniteP1SplittingTarget A N hA S)
      (ordinaryFiniteP1SplittingMap A N hA t S hS c) hi
    decomposition_hom := by rfl }

private theorem splittingFromMap_hom
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS) c)
    (hi : IsIso (C := DerivedCategoryModule A S)
      (ordinaryFiniteP1SplittingMap A N hA t S hS c)) :
    (splittingFromMap A N hA t S hS c hc hi).decomposition.hom =
      ordinaryFiniteP1SplittingMap A N hA t S hS c := by
  unfold splittingFromMap
  rfl

private theorem inverse_trace_naturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {X' Y' Z' : D} (b : X ≅ Y) (b' : X' ≅ Y')
    (e : F.obj Y ⟶ Y') (s : F.obj X ⟶ X') (p : X ⟶ Z) (p' : X' ⟶ Z')
    (r : F.obj Z ⟶ Z') (hsq : F.map b.hom ≫ e = s ≫ b'.hom)
    (hp : s ≫ p' = F.map p ≫ r) :
    F.map (b.inv ≫ p) ≫ r = e ≫ b'.inv ≫ p' := by
  apply (cancel_epi (F.map b.hom)).1
  calc
    F.map b.hom ≫ (F.map (b.inv ≫ p) ≫ r) = F.map p ≫ r := by
      rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id_assoc]
    _ = s ≫ p' := hp.symm
    _ = F.map b.hom ≫ (e ≫ b'.inv ≫ p') := by
      rw [← Category.assoc, hsq]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem biprod_trace_components
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} [HasBinaryBiproduct X Y]
    (b : X ⊞ Y ≅ Z) (v : X ⟶ Z) (w : Y ⟶ Z)
    (hb : b.hom = biprod.desc v w) :
    (v ≫ (b.inv ≫ biprod.snd) = 0) ∧
      (w ≫ (b.inv ≫ biprod.snd) = 𝟙 Y) := by
  have hv : biprod.inl ≫ b.hom = v := by rw [hb, biprod.inl_desc]
  have hw : biprod.inr ≫ b.hom = w := by rw [hb, biprod.inr_desc]
  constructor
  · rw [← hv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.inl_snd]
  · rw [← hw]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.inr_snd]

/-- The supported diagonal classes and the two normalized integrals. This is the
diagonal clause of the arbitrary-base finite projective-line theorem.
Source: blueprint tower P1 adjunction, finite diagonal check
(auxiliary; not a blueprint node). -/
def finiteP1DiagonalProperty (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
    ∃ κ : Ext
      (C := Sheaf
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} A))
      ((lowerStar (ModuleCat.{u + 1} A)
        (Z := ProjectiveLine S)
        (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
      SupportedKummerBoundary A N hA
        (D := ProjectiveLine S) (T := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S)) hI
        (finiteP1_unitOnPullback N
  (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := S)
  ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)) hS) κ ∧
      ∀ a : Bool,
        IsIso (C := DerivedCategoryModule A (ProjectiveLine S))
          (projectiveLineDiagonalAlpha A S a) ∧
        ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
          arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
        𝟙 (ordinaryFiniteUnit A (ProjectiveLine S))

/-- The finite Kummer splitting and both diagonal integrals over every N-invertible base.
The supported boundary fixes the sign through its canonical relative Kummer construction.
The maps alpha are the existing canonical composition identifications, explicitly isomorphisms.

proof.md, levelwise finite diagonal check
(auxiliary; not a blueprint node).

Proof:
1. Use exists_ordinaryFiniteP1SplittingMap, whose universal-Noetherian-base argument
makes the specified twisted-unit/Chern map invertible and natural over all bases.
Use its maps as the decomposition field of the required splitting records.
2. The trace is the inverse decomposition followed by the second projection.
Cancel the pulled-back decomposition in its naturality square; compatibility of the
second projection with the two-summand comparison gives the trace square.
3. For either product projection, the diagonal-chart comparison identifies its
supported class with beta followed by the twisted unit plus the relative hyperplane
Chern adjunct, by ordinaryFiniteP1_diagonal_chern_components. The diagonal ideal and
its supported Kummer representative are the witnesses of that component calculation.
4. The canonical alpha is invertible by isIso_projectiveLineDiagonalAlpha: the
composite inverse image for projection after diagonal is naturally identity, and the
two constant-object units are the composite adjunction unit followed by isomorphisms.
5. The trace kills the first component and sends the Chern component to identity,
by the two injection/projection identities of the biproduct decomposition. Distribute
composition over the component sum to obtain each required integral. This uses no
Noetherian hypothesis on the given base and no detection of general derived arrows
by stalks. -/
theorem exists_arbitraryBaseFiniteP1Integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ArbitraryBaseFiniteP1Splitting A N hA t S hS),
      ArbitraryBaseFiniteP1BaseChange A N hA t d ∧
      ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        finiteP1DiagonalProperty A N hA t d S hS := by
  classical
  obtain ⟨c, hc, hbc⟩ := exists_ordinaryFiniteP1SplittingMap N hN A hA
  let t := projectiveLineTraceTransport N hN A hA
  let d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS := fun S hS ↦
    splittingFromMap A N hA t S hS (c S hS) (hc S hS).1 (hc S hS).2
  have hd (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
      (d S hS).decomposition.hom = ordinaryFiniteP1SplittingMap A N hA t S hS (c S hS) :=
    splittingFromMap_hom A N hA t S hS (c S hS) (hc S hS).1 (hc S hS).2
  clear_value d
  refine ⟨t, d, ?_, ?_⟩
  · rw [ArbitraryBaseFiniteP1BaseChange]
    intro S' S f hS hS'
    have hsquare := hbc f hS hS'
    rw [← hd S hS, ← hd S' hS'] at hsquare
    constructor
    · exact hsquare
    · simpa only [ArbitraryBaseFiniteP1Splitting.trace, Category.assoc] using
        inverse_trace_naturality (ordinaryFinitePullback A (X := S') (Y := S) f)
        (Z := ordinaryFiniteUnit A S) (Z' := ordinaryFiniteUnit A S')
        (d S hS).decomposition (d S' hS').decomposition
        (ordinaryFiniteP1Exchange A f
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
          (ordinaryFinitePushforward A (X := ProjectiveLine S') (Y := S')
        (ProjectiveLine S' ↘ S')).map
            (X := (ordinaryFinitePullback A (X := ProjectiveLine S') (Y := ProjectiveLine S)
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).obj
                ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
            (Y := (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧)
            (ordinaryFiniteShiftedLinePullback A N hA t
              (X := ProjectiveLine S') (Y := ProjectiveLine S)
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS)).hom)
        (ordinaryFiniteP1DecompositionSourceMap A N hA t f hS)
        (biprod.snd (X := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
          (Y := ordinaryFiniteUnit A S))
        (biprod.snd (X := (ordinaryFiniteLine A N hA S')⟦(2 : ℤ)⟧)
          (Y := ordinaryFiniteUnit A S'))
        (ordinaryFiniteUnitPullback A (X := S') (Y := S) f).hom hsquare
        (by
          dsimp only [ordinaryFiniteP1SplittingSource]
          rw [ordinaryFiniteP1DecompositionSourceMap, biprod.lift_snd])
  · intro S hS
    unfold finiteP1DiagonalProperty
    let hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)) :=
      finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS
    obtain ⟨hI, κ, hκ, hcomponents⟩ :=
      ordinaryFiniteP1_diagonal_chern_components N hN A hA t S hS hP
        (finiteP1_unitOnPullback N (X := ProjectiveLine (ProjectiveLine S))
          (Y := ProjectiveLine S) (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S) hP)
        (finiteP1_unitOnPullback N
        (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := S)
        ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)) hS)
        (d (ProjectiveLine S) hP).chern (d (ProjectiveLine S) hP).chern_spec
    refine ⟨hI, κ, hκ, ?_⟩
    intro a
    obtain ⟨β, hβ⟩ := hcomponents a
    refine ⟨isIso_projectiveLineDiagonalAlpha A S a, ?_⟩
    have htransport : arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
        ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫
          (d (ProjectiveLine S) hP).trace := by
      unfold arbitraryBaseFiniteP1DiagonalTrace
      rfl
    rw [htransport]
    have htraces := biprod_trace_components
      (C := DerivedCategoryModule A (ProjectiveLine S))
      (X := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
      (Y := ordinaryFiniteUnit A (ProjectiveLine S))
      (d (ProjectiveLine S) hP).decomposition
      (ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP)
      (ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S)
        (d (ProjectiveLine S) hP).chern)
      (by
        rw [(d (ProjectiveLine S) hP).decomposition_hom]
        unfold ordinaryFiniteP1SplittingMap
        rfl)
    have hcomp := congrArg
      (fun f : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
          (ordinaryFinitePushforward A (X := ProjectiveLine (ProjectiveLine S))
            (Y := ProjectiveLine S) (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
              ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) ↦
        f ≫ (d (ProjectiveLine S) hP).trace) hβ
    simp only [ArbitraryBaseFiniteP1Splitting.trace] at hcomp
    simp only [Preadditive.add_comp, Category.assoc, htraces.1, htraces.2,
      comp_zero, zero_add] at hcomp
    simpa only [ArbitraryBaseFiniteP1Splitting.trace, Category.assoc] using hcomp

end AlgebraicGeometry.Etale
