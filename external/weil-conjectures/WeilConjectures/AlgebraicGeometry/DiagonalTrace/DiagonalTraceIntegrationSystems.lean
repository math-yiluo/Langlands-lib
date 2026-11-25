/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
public import WeilConjectures.CategoryTheory.SixFunctors.SingleTowerEvaluationFaithful
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceLimitWitnessExistence

/-! # The system underlying a completed diagonal integral
Source: diagonal tower trace proof paragraph (2), steps 9--11.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- A completed diagonal integral is the inverse limit of a degree-zero system
endomorphism whose evaluations are identities. This retains the single whole-system
map and its limit comparison, rather than inferring equality from derived evaluations.

Source: diagonal tower trace proof paragraph (2), steps 9--11
(blueprint: lem-sfb-diagonal-trace-integration-systems).
Proof: composition of the ordinary direct images along the diagonal and either
projection is the identity direct image. Their canonical comparison sends sections to
the same sections, giving the normalized supported-source isomorphism. Exactness of
closed pushforward for finite-coefficient systems, followed by exact restriction to
constant scalars, identifies its derived value on the coefficient source with the
ordinary value. The derived composition comparison gives acyclicity of that source.
Compose the strict-system supported diagonal class with the specified strict-system
trace. Evaluation preserves the units and comparisons, and gives the finite Cartier
class and usual projective-line trace. The finite diagonal integral theorem therefore
makes every evaluation the identity. Apply the natural pushforward/limit comparison
to this one system endomorphism. The whole-system characterization of the supplied
completed diagonal and the construction equation of Result identify its limit with
the completed integral. The source comparison is the inverse limit of the same
ordinary composition comparison, giving the displayed square. No assertion that
evaluation is faithful on arbitrary derived objects is used. -/
theorem diagonalTrace_integrationSystems
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (t : Result l (ULift.{u} (Padic l)) f) :
    ∃ a : SupportedSource l Y f t.Rc,
      ∃ s : SingleTowerLimitWitness (DiagonalMod l (ProjectiveLine Y))
        ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map
          (a.hom ≫ t.Rc.R.map δ ≫ t.trace)),
        s.tower = t.restrictionS.F.obj
          (SpTowerClasses.coefficient (ProjectiveLine Y)
            (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y))) ∧
        s.limitFunctor = t.LS.R := by
  obtain ⟨a⟩ := diagonalTrace_supportedSource_exists l Y f hf t
  obtain ⟨s, hs⟩ := diagonalTrace_limitWitness_exists l Y hY D δ hδ f hf t a
  exact ⟨a, s, hs⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
