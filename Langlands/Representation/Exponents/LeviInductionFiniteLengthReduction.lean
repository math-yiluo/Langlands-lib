import Langlands.Representation.Exponents.LeviInductionFiniteLengthStatement
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingStatement
import Langlands.Representation.Exponents.LeviSupercuspidalInductionAssociationStatement
import Langlands.Representation.Exponents.LeviInductionEmbeddings
import Langlands.Representation.Exponents.LeviInductionStages
import Langlands.Representation.Filtration.LengthCriterionProof

/-! # The represented-parabolic assembly for Renard VI.6.2

This internal reduction derives the unchanged finite-length target for normalized
induction from the VI.2.1 embedding statement and the VI.5.4 Theorem. It does not
prove either of them.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The VI.2.1 cuspidal embedding and the VI.5.4 Theorem imply the represented VI.6.2
target. -/
def LeviInductionFiniteLengthReductionStatement : Prop :=
  LeviCuspidalEmbeddingStatement.{u, v} →
  LeviSupercuspidalInductionAssociationStatement.{u, v} →
  LeviInductionFiniteLengthStatement.{u, v}

/-- Embed an irreducible `σ` into `i_Q^M ρ` with `ρ` supercuspidal, induce in stages, and
use finite length of `i_R^G ρ`. -/
theorem leviInductionFiniteLength_reduction :
    LeviInductionFiniteLengthReductionStatement.{u, v} := by
  intro hEmb hAssoc k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  apply leviInduction_preservesFiniteLength_of_irreducibles p l r hp hl hr hmul hG
  intro σ hσ
  obtain ⟨Q, N, V, q, n, s, hq, hn, hs, hmulQ, -, -, ρ, hρ, hρsc, -, f, hf⟩ :=
    hEmb k M hl.isConnectedReductive σ hσ
  let D := LeviParabolicExtensionDatum.ofExtension hG p l r hp hl hr hmul q n s hq hn hs hmulQ
  obtain ⟨e⟩ := D.leviInduction_iso hG p l r hp hl hr hmul q n s hq hn hs hmulQ
  obtain ⟨m, hm⟩ := (hAssoc k G hG D.R N D.W D.R N D.W D.pR D.nR D.rR D.hpR D.hnR D.hrR
    D.hmulR D.pR D.nR D.rR D.hpR D.hnR D.hrR D.hmulR ρ ρ hρ hρsc hρ hρsc).1
  have hR : ((leviInductionFunctor.{u, v} D.pR D.nR D.rR D.hpR D.hrR D.hnR D.hmulR).obj
      ρ).HasFiniteLength :=
    LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength hm
  have hPQ : ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
      ((leviInductionFunctor.{u, v} q n s hq hs hn hmulQ).obj ρ)).HasFiniteLength :=
    IsFiniteLength.of_surjective hR
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (SmoothRep.equivOfIso (e.app ρ)).toIntertwiningMap)
      (SmoothRep.equivOfIso (e.app ρ)).surjective
  exact leviInduction_hasFiniteLength_of_injective p l r hp hl hr hmul f hf hPQ

end Langlands.Aubert.General.RepresentedParabolic
