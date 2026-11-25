/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientQuotients
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerScalarFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerFiniteNormalization
import WeilConjectures.CategoryTheory.SixFunctors.IntegrationTransport

/-! # Every positive uniformizer reduction of the diagonal diagram

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-coefficient-uniformizer-reduction).
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

attribute [local irreducible] QuotientCompatibility quotientLine quotientLineMap
  derivedScalars RestrictionSquare.mate QuotientLineRealization FiniteDiagonalComparison

private theorem scalarFrame_diagram
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X) (d₀ : Diagram Λ Y L)
    (e : ScalarFrame a Y L L' m d₀) :
    ∃ d : Diagram Λ' Y L', Nonempty (ScalarCompatibility a Y L L' m d₀ d) := by
  let Rq := scalarRightDerived Λ' (ProjectiveLine Y ↘ Y)
  let R₁ := scalarRightDerived Λ'
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let R₂ := scalarRightDerived Λ'
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let U := derivedScalars a (diagonalSurface Y)
  let V := derivedScalars a (ProjectiveLine Y)
  let := e.q_iso
  let := e.p₁_iso
  let := e.p₂_iso
  have hlineP : IsIso (e.lineP.shift a) := by
    dsimp only [Endpoint.shift]
    infer_instance
  have hlineW : IsIso (e.lineW.shift a) := by
    dsimp only [Endpoint.shift]
    infer_instance
  let := hlineP
  let := hlineW
  let delta := e.supported.iso.inv ≫ U.map d₀.delta ≫ e.lineW.shift a
  let traceq := inv ((e.q.mate a).app _ ≫ Rq.R.map (e.lineP.shift a)) ≫
    (derivedScalars a Y).map d₀.traceq ≫ (e.units Y).iso.hom
  let trace₁ := inv ((e.p₁.mate a).app _ ≫ R₁.R.map (e.lineW.shift a)) ≫
    V.map d₀.trace₁ ≫ (e.units (ProjectiveLine Y)).iso.hom
  let trace₂ := inv ((e.p₂.mate a).app _ ≫ R₂.R.map (e.lineW.shift a)) ≫
    V.map d₀.trace₂ ≫ (e.units (ProjectiveLine Y)).iso.hom
  have hdelta : U.map d₀.delta ≫ e.lineW.shift a =
      e.supported.iso.hom ≫ delta := by
    dsimp only [delta]
    simp only [Iso.hom_inv_id_assoc]
  have htraceq : (derivedScalars a Y).map d₀.traceq ≫ (e.units Y).iso.hom =
      (e.q.mate a).app _ ≫ Rq.R.map (e.lineP.shift a) ≫ traceq := by
    dsimp only [traceq]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₁ : V.map d₀.trace₁ ≫ (e.units (ProjectiveLine Y)).iso.hom =
      (e.p₁.mate a).app _ ≫ R₁.R.map (e.lineW.shift a) ≫ trace₁ := by
    dsimp only [trace₁]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₂ : V.map d₀.trace₂ ≫ (e.units (ProjectiveLine Y)).iso.hom =
      (e.p₂.mate a).app _ ≫ R₂.R.map (e.lineW.shift a) ≫ trace₂ := by
    dsimp only [trace₂]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  let d : Diagram Λ' Y L' :=
    { Rq := Rq
      R₁ := R₁
      R₂ := R₂
      q_canonical := rfl
      p₁_canonical := rfl
      p₂_canonical := rfl
      q_unit := by intro K; exact Category.comp_id _
      p₁_unit := by intro K; exact Category.comp_id _
      p₂_unit := by intro K; exact Category.comp_id _
      delta := delta
      traceq := traceq
      trace₁ := trace₁
      trace₂ := trace₂
      support₁ := e.support₁
      support₂ := e.support₂
      integration₁ := integration_transport d₀.R₁.R R₁.R U V
        (e.p₁.mate a) e.supported.iso.hom (e.lineW.shift a)
        (e.units (ProjectiveLine Y)).iso d₀.support₁.hom d₀.delta d₀.trace₁
        e.support₁.hom delta trace₁ e.source₁ hdelta htrace₁ d₀.integration₁
      integration₂ := integration_transport d₀.R₂.R R₂.R U V
        (e.p₂.mate a) e.supported.iso.hom (e.lineW.shift a)
        (e.units (ProjectiveLine Y)).iso d₀.support₂.hom d₀.delta d₀.trace₂
        e.support₂.hom delta trace₂ e.source₂ hdelta htrace₂ d₀.integration₂ }
  let scalar : ScalarCompatibility a Y L L' m d₀ d :=
    { units := e.units
      lineP := e.lineP
      lineW := e.lineW
      supported := e.supported
      q := { square := e.q, comparison_iso := e.q_iso, trace := htraceq }
      p₁ := { square := e.p₁, comparison_iso := e.p₁_iso, trace := htrace₁ }
      p₂ := { square := e.p₂, comparison_iso := e.p₂_iso, trace := htrace₂ }
      delta := hdelta }
  exact ⟨d, ⟨scalar⟩⟩

/-- Identify one arbitrary positive uniformizer reduction with its finite
Cartier class and normalized trace. This result does not construct integral,
rational or algebraic-closure families.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), quotient assertion.
(blueprint: lem-diagonal-coefficient-uniformizer-reduction).

Proof: The maximal ideal is generated by pi and contains l. Thus l^(n+1)
kills the pi^(n+1) quotient, as diagonalUniformizer_annihilator proves. Reduce
the whole completed class and trace systems first modulo l^(n+1), using the
projection-normalized comparisons of the diagonal limit and trace theorems.
Then extend scalars to O_E/pi^(n+1). The normalized finite coefficient
realization identifies its supported source with the ordinary finite constant
source. The root projections identify the reduced integral line with the
finite Tate line, using the same killing exponent. Cartier scalar
compatibility identifies the transported arrow with the canonical positive
Cartier arrow. The unit/Chern splitting transports to the finite splitting;
inverting it and projecting to the constant summand identifies the trace.
Right-derived units fix both direct-image comparisons, so these are the
canonical scalar mates. Transporting the two integration identities supplies
the two identities in the quotient diagram. Scalar-extension associativity
identifies this diagram with the quotient of family.integral E through its
recorded Z_l-to-integral square. This works at each positive pi exponent,
including ramified levels outside the ell-power cofinal subsystem. -/
theorem diagonalCoefficient_uniformizerFiniteComparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (reference : Reference l Y δ family)
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    (hfinite : Finite (ULift.{u + 1} (completedResidue l E π n)))
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (hWpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)))
    (rootsP : FiniteRoots (ProjectiveLine Y) (l ^ (n + 1)))
    (rootsW : FiniteRoots (diagonalSurface Y) (l ^ (n + 1))) :
    ∃ d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        Y (quotientLine l E π n),
      Nonempty (ScalarCompatibility (quotientMap l E π n) Y
        (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
        (quotientLineMap l E π n) (family.integral E) d) ∧
      QuotientCompatibility l Y E π n d := by
  obtain ⟨e⟩ := diagonalUniformizer_scalarFrame l Y hY E π hπ n (family.integral E)
  obtain ⟨d, ⟨scalar⟩⟩ := scalarFrame_diagram (quotientMap l E π n) Y
    (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
    (quotientLineMap l E π n) (family.integral E) e
  obtain ⟨eY, eP, eW, lineP, lineW, hfiniteComparison⟩ :=
    diagonalUniformizer_finiteNormalization l Y hY D hcompletion hsystem δ hδ
      family reference E π hπ n hfinite hA hYpow hWpow rootsP rootsW d scalar
  refine ⟨d, ⟨scalar⟩, ?_⟩
  unfold QuotientCompatibility
  exact ⟨hfinite, n, hA, hYpow, hWpow, eY, eP, eW, lineP, lineW, hfiniteComparison⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
