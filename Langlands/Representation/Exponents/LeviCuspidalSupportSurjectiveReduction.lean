import Langlands.Representation.Exponents.LeviCuspidalSupportSurjectiveStatement
import Langlands.Representation.Exponents.LeviInductionFiniteLengthStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationStatement
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Category.RenardFinitenessProof
import Langlands.Representation.Filtration.FiniteLengthIrreducibleSources

/-! # The represented-parabolic assembly for Renard VI.7.1

This internal reduction derives the exact published surjectivity and finite-family
target from four global inputs. It does not discharge those inputs.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Induction finite length, finite-length admissibility, Jacquet admissibility
and supercuspidal subquotient realization imply the published VI.7.1 target. -/
def LeviCuspidalSupportSurjectiveReductionStatement : Prop :=
  LeviInductionFiniteLengthStatement.{u, v} →
  RationalPointsFiniteLengthAdmissibleStatement.{u, v} →
  ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
  RepresentedSupercuspidalSubquotientRealizationStatement.{u, v} →
  LeviCuspidalSupportSurjectiveStatement.{u, v}

/-- Apply actual Frobenius reciprocity to an irreducible subrepresentation
of the induction, and to each quotient supplied by supercuspidal realization. -/
theorem leviCuspidalSupportSurjective_reduction :
    LeviCuspidalSupportSurjectiveReductionStatement.{u, v} := by
  intro hInd hAdmissible hJacquetAdmissible hRealize k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) :=
    leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ hρsc
  let := hρ
  have : Nontrivial ρ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule
  let I := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  have hI : I.HasFiniteLength :=
    hInd k G hG P M U p l r hp hl hr hmul ρ
      (SmoothRep.hasFiniteLength_of_isIrreducible hρ)
  constructor
  · have : Nontrivial (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm ρ) :=
      ‹Nontrivial ρ›
    have : Nontrivial I :=
      nontrivial_normalizedInduction
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (continuous_projection_pointImage p l r hp hl hr hmul)
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm ρ)
    obtain ⟨π, hπ, i, hi⟩ :=
      SmoothRep.RenardIrreducibleExistence.exists_irreducible_subrepresentation_of_finiteLength
        I ((SmoothRep.renardFiniteLength_iff I).mpr hI)
    let := hπ
    have : Nontrivial π :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
    have hi0 : SmoothRep.hom i ≠ 0 := by
      intro hz
      exact (LinearMap.ne_zero_of_injective hi)
        (congrArg Representation.IntertwiningMap.toLinearMap hz)
    obtain ⟨e, _⟩ := leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul π ρ
    have he0 : e (SmoothRep.hom i) ≠ 0 := by
      intro hz
      exact hi0 (e.injective (hz.trans (map_zero e).symm))
    exact ⟨π, hπ, e (SmoothRep.hom i),
      (Representation.IsIrreducible.surjective_or_eq_zero _).resolve_right he0⟩
  · obtain ⟨n, π₀, _, hπ₀⟩ :=
      SmoothRep.finiteLengthIrreducibleSources.{0, u, max u v, v}
        ℂ (rationalPoints G) I hI
    refine ⟨n, π₀, ?_⟩
    intro π hπ hsub
    have hπAdmissible := hAdmissible k G hG π
      (SmoothRep.hasFiniteLength_of_isIrreducible hπ)
    have hJ := hJacquetAdmissible k G hG P M U p l r hp hl hr hmul π hπAdmissible
    have hJ' : ((leviJacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible :=
      isAdmissible_comp_continuousMulEquiv
        ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
        (leviPointsEquiv p l hp hl) hJ
    obtain ⟨q, hq⟩ :=
      (hRealize k M hl.isConnectedReductive
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π) ρ hJ' hρ hρsc hsub).2
    have hq0 : SmoothRep.hom q ≠ 0 := by
      intro hz
      exact (LinearMap.ne_zero_of_surjective hq)
        (congrArg Representation.IntertwiningMap.toLinearMap hz)
    obtain ⟨e, _⟩ := leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul π ρ
    have he0 : e.symm (SmoothRep.hom q) ≠ 0 := by
      intro hz
      exact hq0 (e.symm.injective (hz.trans (map_zero e.symm).symm))
    exact hπ₀ π hπ (e.symm (SmoothRep.hom q)) he0

end Langlands.Aubert.General.RepresentedParabolic
