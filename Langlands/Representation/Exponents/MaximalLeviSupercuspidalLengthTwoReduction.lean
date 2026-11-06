import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLengthTwoStatement
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.LengthTwoExtraction

/-! # Nonzeroness and endpoint extraction for represented induction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Nonzero

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance representedNonzeroPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Actual represented normalized induction has a nontrivial carrier whenever
the supplied smooth representation of the Levi's own point group does. -/
theorem leviInduction_nontrivial
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    [Nontrivial ρ] :
    letI := leviPointTopology l hl
    Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) := by
  let := leviPointTopology l hl
  have : Nontrivial (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm ρ) := by
    change Nontrivial ρ
    infer_instance
  exact nontrivial_normalizedInduction
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm ρ)

end Nonzero

/-- The only remaining representation-theoretic input to actual two-endpoint
extraction is the represented length bound. Nonzeroness is proved above. -/
theorem maximalLeviSupercuspidalLengthTwo_of_lengthBound
    (hbound : MaximalLeviSupercuspidalInductionLengthBoundStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  let := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hsc hred
  have : Nontrivial ρ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M))
    ρ.representation.asModule
  have : Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) :=
    leviInduction_nontrivial p l r hp hl hr hmul ρ
  obtain ⟨π₁, π₂, h₁, h₂, f, g, hfg⟩ :=
    SmoothRep.exists_two_irreducible_factors_of_length_le_two
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)
      (hbound k G hG P M U p l r hp hl hr hmul hproper hmax ρ hirr hsc) hred
  exact ⟨π₁.val, π₂.val, h₁, h₂, SmoothRep.ofHom f, SmoothRep.ofHom g, hfg⟩

end Langlands.Aubert.General.RepresentedParabolic
