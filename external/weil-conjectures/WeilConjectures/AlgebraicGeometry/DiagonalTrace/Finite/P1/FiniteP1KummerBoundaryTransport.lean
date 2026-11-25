/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteQuotientDerivedDetection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryKummerBoundary
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerEvaluated
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerUnitEquation

/-! # Transport of the finite Kummer boundary comparison

Source: blueprint latest, diagonal-tower trace proof (1), scalar Kummer
normalization in paragraph (1).
(blueprint: lem-sfb-finite-p1-kummer-boundary-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite boundary equality at the pulled-back hyperplane class. -/
def FiniteP1BoundaryData
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] : Prop :=
  FiniteKummerBoundary l E X n cX.kummer
    (Scheme.Pic.mapHom e.hom (hyperplanePic S))
    (evaluatedChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n)

/--
A finite boundary equality transports through the normalized coefficient and
site comparisons to the displayed derived equality. The comparison t is the
explicit normalized coordinate; mere existence of an endpoint isomorphism does
not specify its effect on the positive class. The statement isolates
the scalar Kummer step from construction of the line comparison isomorphism.
Source: diagonal-tower trace (1), scalar Kummer normalization in paragraph (1).
(blueprint: lem-sfb-finite-p1-kummer-boundary-transport).
-/
-- STATEMENT-DISPUTED: the old signature allowed arbitrary t, independently of hb.
-- Composing a normalized t with a nontrivial scalar automorphism changes the class.
-- The explicit normalization ht repairs that missing hypothesis.
theorem finiteP1_kummer_chern_realization_of_boundary
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2))
    (ht : t = finiteP1KummerCoordinate l E n e cX hS c)
    (hb : FiniteP1BoundaryData l E e cX n) :
    (SpTowerShriek.Ev l E X n).map
        (firstChern l E cX
          (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
      (finiteOverUnitCoordinate l E n e c).hom ≫
        (finiteOverRealization l E n e).map
          ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map
            (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _)
              (ULift.ext (coefficient_annihilates l E n)) S
              (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))) := by
  subst t
  have hclass : evaluatedChern l E cX
      (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n =
      finiteP1OrdinaryKummerArrow l E n e hS c := by
    obtain ⟨a₁, β₁, ha₁, hβ₁, h₁⟩ := hb
    obtain ⟨a₂, β₂, ha₂, hβ₂, h₂⟩ :=
      finiteP1_ordinary_kummer_boundary l E e cX.kummer hS n c
    have hβ : β₁ = β₂ := eq_of_heq (hβ₁.trans hβ₂.symm)
    have ha₁' := eq_of_heq ha₁
    have ha₂' := eq_of_heq ha₂
    subst hβ ha₁' ha₂'
    exact finiteQuotient_detects_derived_arrows l E X n (finiteLine l E X n)
      (h₁.trans h₂.symm)
  have hh := congrArg (fun a ↦
    ((SpTowerShriek.ev l E X n).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      a ≫ (finiteKummerLineCoordinate l E n e hS c).hom) hclass
  rw [finiteP1_evaluatedChern_eq l E cX _ n] at hh
  rw [finiteP1_unit_coordinate_eq l E e n c]
  simpa only [finiteP1KummerCoordinate, Iso.trans_hom, finiteP1OrdinaryKummerArrow,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh

end AlgebraicGeometry.ProEtale.DiagonalTrace
