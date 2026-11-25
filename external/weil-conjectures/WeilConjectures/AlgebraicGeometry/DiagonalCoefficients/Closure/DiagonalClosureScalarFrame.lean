/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerScalarFrame
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerScalarFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureLineComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedScalarSource

/-! # The scalar frame for one finite field to the algebraic closure

Source: diagonal coefficient changes, paragraph (2).
(blueprint: lem-diagonal-closure-scalar-frame).
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

attribute [local irreducible] canonicalDiagonalRightDerived RestrictionSquare.mate
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  derivedScalars regularEndpoint

private theorem scalarFrame_of_lineComparisons
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X) (d : Diagram Λ Y L)
    (lineP : Endpoint a (L (ProjectiveLine Y)) (L' (ProjectiveLine Y))
      (m (ProjectiveLine Y)))
    (lineW : Endpoint a (L (diagonalSurface Y)) (L' (diagonalSurface Y))
      (m (diagonalSurface Y)))
    (q : RestrictionSquare a (ProjectiveLine Y ↘ Y) d.Rq
      (scalarRightDerived Λ' (ProjectiveLine Y ↘ Y)))
    (p₁ : RestrictionSquare a
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁
      (scalarRightDerived Λ'
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))))
    (p₂ : RestrictionSquare a
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂
      (scalarRightDerived Λ'
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))))
    (hq : IsIso ((q.mate a).app
      (((DerivedCategory.singleFunctor _ 0).obj (L (ProjectiveLine Y)))⟦(2 : ℤ)⟧)))
    (hp₁ : IsIso ((p₁.mate a).app
      (((DerivedCategory.singleFunctor _ 0).obj (L (diagonalSurface Y)))⟦(2 : ℤ)⟧)))
    (hp₂ : IsIso ((p₂.mate a).app
      (((DerivedCategory.singleFunctor _ 0).obj (L (diagonalSurface Y)))⟦(2 : ℤ)⟧))) :
    Nonempty (ScalarFrame a Y L L' m d) := by
  let c := regularEndpoint a
  obtain ⟨e₁, s₁, hs₁⟩ := diagonal_supported_scalar_source a Y (c (ProjectiveLine Y))
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁ p₁ d.support₁
  obtain ⟨e₂, s₂, hs₂⟩ := diagonal_supported_scalar_source a Y (c (ProjectiveLine Y))
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂ p₂ d.support₂
  rw [endpoint_hom_unique a e₂ e₁] at hs₂
  exact ⟨{
    units := c
    lineP := lineP
    lineW := lineW
    supported := e₁
    q := q
    p₁ := p₁
    p₂ := p₂
    q_iso := hq
    p₁_iso := hp₁
    p₂_iso := hp₂
    support₁ := s₁
    support₂ := s₂
    source₁ := hs₁
    source₂ := hs₂ }⟩

attribute [local irreducible] spRationalTwist spQbarTwist closureLineMap

/-- Construct only the scalar endpoints and normalized direct-image comparisons
for one finite-field inclusion into the closure. No class, trace, integration
identity, family or compatibility between finite fields is asserted.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), bounded filtered colimit.
(blueprint: lem-diagonal-closure-scalar-frame).

Proof: The finite subextensions containing E form a filtered cofinal subposet.
Their coefficient colimit is the prescribed condensed algebraic closure, and
their root-line colimit is spQbarTwist, with exactly closureLineMap as each leg.
Finite field extension of the rational root line is scalar extension: use finite
freeness on each integral root level and then localization. Taking the filtered
colimit gives the ordinary scalar-extension isomorphism from E to the closure.
The rational root line is locally free of rank one and hence flat. The K-flat
single-complex comparison turns the ordinary unit and line comparisons into
Endpoint records normalized by their derived scalar/restriction adjoints.
The regular-module endpoint is normalized scalar multiplication, at every scheme.

Restriction of coefficients commutes with direct image; derive this square with
its full universal unit, transporting the input model by its canonical functor
and unit equalities. For each of the three projections, bounded continuity on
the filtered finite-extension diagram identifies its scalar mate with the
colimit of the finite-free direct-image comparisons. The shifted root lines have
common lower bound -2 and the projections are qcqs, so this mate is invertible
on precisely the shifted lines required by ScalarFrame. No continuity assertion
on arbitrary unbounded objects is used. The target models are scalarRightDerived.
Apply diagonal_supported_scalar_source separately to the two projections to get
the supported endpoint and normalized sources. Endpoint uniqueness by adjunction
injectivity identifies the two supported endpoint homs, so both source equations
use the same endpoint. Assemble the frame. This works for the bottom field and
empty schemes; the construction never uses a diagonal class or a trace. -/
theorem diagonalClosure_scalarFrame
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤))) (E : PadicAlgCl.FiniteIntermediateField l)
    (d : Diagram (Profinite.continuousMapRingObj.{u} E.1) Y
      (fun X ↦ spRationalTwist X l E)) :
    Nonempty (ScalarFrame (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y
      (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
      (closureLineMap l E) d) := by
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using
      hP.map (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).appTop.hom
  obtain ⟨lineP, q, hq⟩ := diagonalClosure_lineComparison l E
    (ProjectiveLine Y ↘ Y) hP d.Rq d.q_canonical d.q_unit
  obtain ⟨lineW, p₁, hp₁⟩ := diagonalClosure_lineComparison l E
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    hW d.R₁ d.p₁_canonical d.p₁_unit
  obtain ⟨_, p₂, hp₂⟩ := diagonalClosure_lineComparison l E
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    hW d.R₂ d.p₂_canonical d.p₂_unit
  exact scalarFrame_of_lineComparisons a Y
    (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
    (closureLineMap l E) d lineP lineW q p₁ p₂ hq hp₁ hp₂

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
