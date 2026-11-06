import Langlands.Representation.Exponents.LeviCuspidalSupportAssociationStatement
import Langlands.Representation.Exponents.LeviSupercuspidalInductionAssociationStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationStatement
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # The represented-parabolic assembly for the lemma of Renard VI.7.1

This internal reduction derives the exact published association target from four
global propositions. It does not discharge those propositions.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Finite-length admissibility, Jacquet admissibility, supercuspidal realization
and the VI.5.4 association theorem imply the published VI.7.1 lemma. -/
def LeviCuspidalSupportAssociationReductionStatement : Prop :=
  RationalPointsFiniteLengthAdmissibleStatement.{u, v} →
  ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
  RepresentedSupercuspidalSubquotientRealizationStatement.{u, v} →
  LeviSupercuspidalInductionAssociationStatement.{u, v} →
  LeviCuspidalSupportAssociationStatement.{u, v}

/-- Quotient realization and Frobenius embed a lift of the given irreducible
representation into both inductions; VI.5.4 then gives association. -/
theorem leviCuspidalSupportAssociation_reduction :
    LeviCuspidalSupportAssociationReductionStatement.{u, v} := by
  intro hAdmissible hJacquetAdmissible hRealize hAssociate k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P₁ M₁ U₁ P₂ M₂ U₂ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
  have := hl₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
  have : LocallyCompactSpace (rationalPoints M₁) :=
    leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
  have : NonarchimedeanGroup (rationalPoints M₁) :=
    leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
  have := hl₂.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
  have : LocallyCompactSpace (rationalPoints M₂) :=
    leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
  have : NonarchimedeanGroup (rationalPoints M₂) :=
    leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
  intro π ρ₁ ρ₂ hπ hρ₁ hρ₁sc hsub₁ hρ₂ hρ₂sc hsub₂
  let := hπ
  let := hρ₁
  let := hρ₂
  have : Nontrivial ρ₁ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M₁)) ρ₁.representation.asModule
  have : Nontrivial ρ₂ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M₂)) ρ₂.representation.asModule
  have hπAdmissible := hAdmissible k G hG π
    (SmoothRep.hasFiniteLength_of_isIrreducible hπ)
  have hJ₁ := hJacquetAdmissible k G hG P₁ M₁ U₁
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ π hπAdmissible
  have hJ₁' : ((leviJacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj π).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj π).representation
      (leviPointsEquiv p₁ l₁ hp₁ hl₁) hJ₁
  obtain ⟨q₁, hq₁⟩ :=
    (hRealize k M₁ hl₁.isConnectedReductive
      ((leviJacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj π)
      ρ₁ hJ₁' hρ₁ hρ₁sc hsub₁).2
  have hq₁0 : SmoothRep.hom q₁ ≠ 0 := by
    intro hz
    exact (LinearMap.ne_zero_of_surjective hq₁)
      (congrArg Representation.IntertwiningMap.toLinearMap hz)
  obtain ⟨e₁, _⟩ :=
    leviFrobeniusReciprocity k G hG P₁ M₁ U₁ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ π ρ₁
  have he₁0 : e₁.symm (SmoothRep.hom q₁) ≠ 0 := by
    intro hz
    exact hq₁0 (e₁.symm.injective (hz.trans (map_zero e₁.symm).symm))
  have hi₁ : Function.Injective (e₁.symm (SmoothRep.hom q₁)) :=
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right he₁0
  have hJ₂ := hJacquetAdmissible k G hG P₂ M₂ U₂
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ π hπAdmissible
  have hJ₂' : ((leviJacquetFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj π).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj π).representation
      (leviPointsEquiv p₂ l₂ hp₂ hl₂) hJ₂
  obtain ⟨q₂, hq₂⟩ :=
    (hRealize k M₂ hl₂.isConnectedReductive
      ((leviJacquetFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj π)
      ρ₂ hJ₂' hρ₂ hρ₂sc hsub₂).2
  have hq₂0 : SmoothRep.hom q₂ ≠ 0 := by
    intro hz
    exact (LinearMap.ne_zero_of_surjective hq₂)
      (congrArg Representation.IntertwiningMap.toLinearMap hz)
  obtain ⟨e₂, _⟩ :=
    leviFrobeniusReciprocity k G hG P₂ M₂ U₂ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ π ρ₂
  have he₂0 : e₂.symm (SmoothRep.hom q₂) ≠ 0 := by
    intro hz
    exact hq₂0 (e₂.symm.injective (hz.trans (map_zero e₂.symm).symm))
  have hi₂ : Function.Injective (e₂.symm (SmoothRep.hom q₂)) :=
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right he₂0
  let σ := SmoothRep.universeLift.{u} π
  let eπ := SmoothRep.universeLiftEquiv.{u} π
  have hσ : σ.IsIrreducible := (SmoothRep.isIrreducible_universeLift_iff π).mpr hπ
  have hσ₁ : SmoothRep.IsSubquotient σ
      ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj ρ₁) :=
    SmoothRep.IsSubrepresentation.isSubquotient
      ⟨SmoothRep.ofHom ((e₁.symm (SmoothRep.hom q₁)).comp eπ.symm.toIntertwiningMap),
        hi₁.comp eπ.symm.injective⟩
  have hσ₂ : SmoothRep.IsSubquotient σ
      ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj ρ₂) :=
    SmoothRep.IsSubrepresentation.isSubquotient
      ⟨SmoothRep.ofHom ((e₂.symm (SmoothRep.hom q₂)).comp eπ.symm.toIntertwiningMap),
        hi₂.comp eπ.symm.injective⟩
  have hA := (hAssociate k G hG P₁ M₁ U₁ P₂ M₂ U₂
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    ρ₁ ρ₂ hρ₁ hρ₁sc hρ₂ hρ₂sc).2
  apply (hA.out 4 1).mp
  exact ⟨σ, hσ, hσ₁, hσ₂⟩

end Langlands.Aubert.General.RepresentedParabolic
