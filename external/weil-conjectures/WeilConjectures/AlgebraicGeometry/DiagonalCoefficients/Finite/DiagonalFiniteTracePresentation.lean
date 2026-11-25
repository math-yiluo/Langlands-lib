/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteArrowEquations
import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPushSquare

/-! # Constructing finite trace presentations at generic coefficients

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-finite-trace-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The canonical finite right-derived model, full normalized square and positive splitting.
Source: coefficient changes (blueprint: lem-diagonal-finite-trace-presentation).
Proof: choose the published right-derived functor with its canonical cochain unit.
Its unit normalization is composition with the identity. Derive the supplied
ordinary square by uniqueness of right-derived functors under exact equivalences.
The proved projective-line decomposition supplies the positive splitting and its
specified hom. Insert these data into the trace presentation. -/
theorem finiteTracePresentation_exists
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (l : ℕ) (hl : l.Prime) (r : ℕ) (hr : 0 < r) (hA : ((l ^ r : ℕ) : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit ((l ^ r : ℕ) : Γ(Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (ordinarySquare : FiniteOrdinaryPushSquare R A (ProjectiveLine Y ↘ Y) eP eY) :
    Nonempty (FiniteTracePresentation R A (l ^ r) (pow_pos hl.pos r) hA Y hY L d eY eP) := by
  let Rq := canonicalDiagonalRightDerived
    (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y))
  have q_canonical : Rq.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y) := rfl
  have hcanonical : IsCanonicalRightDerived _ Rq q_canonical := by
    intro K
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  obtain ⟨derived⟩ := diagonalExactSquare_exists _ _ eP.F eY.F d.Rq Rq
    ordinarySquare.ordinary
  let q_square : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY d.Rq Rq :=
    { ordinary := ordinarySquare.ordinary
      ordinary_normalization := ordinarySquare.normalization
      derived := derived }
  obtain ⟨b, hb, _⟩ := geoP1Cohomology l hl r hr A hA
  exact ⟨{ Rq := Rq
           q_canonical := q_canonical
           hcanonical := hcanonical
           q_square := q_square
           splitting := b Y hY
           hsplitting := (hb Y hY).2 }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
