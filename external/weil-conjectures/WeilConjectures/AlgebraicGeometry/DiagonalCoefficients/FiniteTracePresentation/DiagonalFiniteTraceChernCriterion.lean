/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteArrowEquations
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Reconstructing a finite trace from its Chern degree

Source: diagonal tower trace proof, paragraph (1), inverse splitting and projection.
(blueprint: lem-diagonal-finite-trace-chern-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The isomorphism underlying the existing shifted-line comparison.
Source: the exact single and shift comparisons in the finite trace presentation.
(blueprint: lem-diagonal-finite-trace-chern-criterion). -/
@[irreducible]
def FiniteRealization.shiftedLineIso
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    (N : ℕ) (hA : (N : A) = 0) (M : Modules R X)
    (i : e.F.obj M ≅ geoCartierLine A N hA X) :
    e.F.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧) ≅ geoP1Twist A N hA X 1 2 :=
  (e.F.mapDerivedCategory.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso ((e.F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso i) ≪≫
    (finiteLineComparison A N hA X).symm

private theorem shiftedLineIso_hom
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    (N : ℕ) (hA : (N : A) = 0) (M : Modules R X)
    (i : e.F.obj M ≅ geoCartierLine A N hA X) :
    (e.shiftedLineIso N hA M i).hom = e.shiftedLine N hA M i := by
  simp only [FiniteRealization.shiftedLineIso, FiniteRealization.shiftedLine,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R] (A : Type (u + 1)) [CommRing A]

/-- The fully normalized isomorphism from a realized pushforward to the finite model.
This simply composes the three existing comparison isomorphisms.
Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-finite-trace-chern-criterion). -/
@[irreducible]
def FiniteTracePresentation.comparison [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (eY : FiniteRealization R A Y)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP) :
    eY.F.mapDerivedCategory.obj
      (d.Rq.R.obj (((DerivedCategory.singleFunctor _ 0).obj
        (L (ProjectiveLine Y)))⟦(2 : ℤ)⟧)) ≅
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
        (geoP1Twist A N hA (ProjectiveLine Y) 1 2) :=
  p.q_square.derived.iso.app _ ≪≫
    p.Rq.R.mapIso (eP.shiftedLineIso N hA (L (ProjectiveLine Y)) lineP) ≪≫
    (eqToIso p.q_canonical).app _

/-- The supplied trace in the canonical finite pushforward and coefficient-unit model.
All data are explicit composites of the supplied isomorphisms and the supplied trace.
Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-finite-trace-chern-criterion). -/
@[irreducible]
def FiniteTracePresentation.realizedTrace [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (eY : FiniteRealization R A Y)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP) :
    (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
      (geoP1Twist A N hA (ProjectiveLine Y) 1 2) ⟶ geoP1Unit A Y :=
  (p.comparison R A N hN hA Y hY L d eY eP lineP).inv ≫
    eY.F.mapDerivedCategory.map d.traceq ≫ eY.derivedUnit

/-- The single Chern-component test, kept at generic coefficients to share instances.
Source: diagonal tower trace proof paragraph (1), second summand of the splitting.
(blueprint: lem-diagonal-finite-trace-chern-criterion). -/
@[irreducible]
def FiniteTraceChernDegree [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (eY : FiniteRealization R A Y)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP) : Prop :=
  biprod.inr ≫ geoP1TwistedMap A N hN hA Y hY ≫
    p.realizedTrace R A N hN hA Y hY L d eY eP lineP = 𝟙 _

private theorem comparison_hom [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (eY : FiniteRealization R A Y)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP) :
    (p.comparison R A N hN hA Y hY L d eY eP lineP).hom =
      p.q_square.derived.iso.hom.app _ ≫
        p.Rq.R.map (eP.shiftedLine N hA (L (ProjectiveLine Y)) lineP) ≫
          (eqToIso p.q_canonical).hom.app _ := by
  simp only [FiniteTracePresentation.comparison, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, shiftedLineIso_hom]

private theorem positive_to_unit_zero (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    (f : geoP1Twist A N hA Y 1 2 ⟶ geoP1Unit A Y) : f = 0 := by
  let C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)
  let single := DerivedCategory.singleFunctor C 0
  let e := finiteLineComparison A N hA Y
  let e' := finiteUnitComparison A Y
  let : DerivedCategory.IsLE (geoP1Twist A N hA Y 1 2) (-2) := by
    let : DerivedCategory.IsLE
        ((single.obj (geoCartierLine A N hA Y))⟦(2 : ℤ)⟧) (-2) :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2) (by decide)
    exact DerivedCategory.TStructure.t.isLE_of_iso e.symm (-2)
  let : DerivedCategory.IsGE (geoP1Unit A Y) 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso e'.symm 0
  exact DerivedCategory.TStructure.t.zero f (-2) 0 (by decide)

/-- A finite trace is determined by degree one on the Chern summand; its other
component vanishes by the canonical t-structure, without a coefficient comparison.

Source: diagonal tower trace proof paragraph (1), twisting the decomposition and
projecting to its second summand; the source's inverse-splitting argument.
(blueprint: lem-diagonal-finite-trace-chern-criterion).

Proof: after the normalized pushforward/line comparison, write t for the supplied
trace. Every arrow from the positive finite line shifted by two to the coefficient
unit vanishes: the source is in degrees at most -2 and the target in degrees at
least zero. Thus the first component of splitting.hom followed by t is zero.
The hypothesis and hsplitting make its second component the identity. Biproduct
extensionality gives splitting.hom followed by t equal to the second projection.
Cancel the splitting isomorphism to obtain t = splitting.inv followed by the second
projection. Finally cancel the normalized pushforward comparison to return to the
supplied models. The argument works for the zero ring and the empty scheme. -/
theorem finitePresentedTraceEquation_of_chern [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (eY : FiniteRealization R A Y)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP)
    (hchern : FiniteTraceChernDegree R A N hN hA Y hY L d eY eP lineP p) :
    FinitePresentedTraceEquation R A N hN hA Y hY L d eY eP lineP p := by
  unfold FiniteTraceChernDegree at hchern
  let t := p.realizedTrace R A N hN hA Y hY L d eY eP lineP
  have ht : t = geoP1Trace A N hA Y p.splitting := by
    apply (cancel_epi p.splitting.hom).mp
    apply biprod.hom_ext'
    · simp only [geoP1Trace, Iso.hom_inv_id_assoc, biprod.inl_snd]
      exact positive_to_unit_zero A N hA Y _
    · simp only [geoP1Trace, Iso.hom_inv_id_assoc, biprod.inr_snd]
      simpa only [p.hsplitting] using hchern
  have hraw : eY.F.mapDerivedCategory.map d.traceq ≫ eY.derivedUnit =
      (p.comparison R A N hN hA Y hY L d eY eP lineP).hom ≫
        geoP1Trace A N hA Y p.splitting := by
    rw [← ht]
    simp only [t, FiniteTracePresentation.realizedTrace, Iso.hom_inv_id_assoc]
  unfold FinitePresentedTraceEquation FiniteProjectiveTraceEquation
  rw [comparison_hom] at hraw
  simpa only [Category.assoc] using hraw

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
