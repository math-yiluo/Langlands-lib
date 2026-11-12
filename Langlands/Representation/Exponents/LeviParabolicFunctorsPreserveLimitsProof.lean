import Langlands.Representation.Exponents.LeviParabolicFunctorsPreserveLimitsStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Exponents.LeviInductionLimits
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Aubert.General.InductionColimits
import Langlands.Representation.Plancherel.RationalModerateGrowthUniformization

/-! # Proof of limit and colimit preservation by the normalized parabolic functors

Renard 2026, VI.1.2 Corollary, for represented parabolics.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

section Colimits

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance leviInductionColimitsPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction on the actual Levi points preserves small colimits when the
parabolic quotient is compact. -/
theorem leviInductionFunctor_preservesColimits_of_compactSpace
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))] :
    let := leviPointTopology l hl
    PreservesColimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  let e := leviPointsEquiv p l hp hl
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : (SmoothRep.pullbackFunctor.{u, u, v} e.symm).IsEquivalence :=
    (SmoothRep.pullbackEquivalence e.symm).isEquivalence_functor
  have := normalizedInductionFunctor_preservesColimits.{u, v}
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (Plancherel.rationalPoint_compactOpenCofinal k G)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
  change PreservesColimitsOfSize.{v, v}
    (SmoothRep.pullbackFunctor e.symm ⋙ normalizedInductionFunctor _ _)
  infer_instance

end Colimits

/-- Renard VI.1.2 Corollary from compactness of every represented parabolic quotient. -/
theorem leviParabolicFunctorsPreserveLimits_of_quotientCompact
    (hC : ArbitraryParabolicQuotientCompactStatement.{u}) :
    LeviParabolicFunctorsPreserveLimitsStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hC k G hG P p hp
  exact ⟨leviInductionFunctor_preservesLimits p l r hp hr hl hmul,
    leviInductionFunctor_preservesColimits_of_compactSpace hG p l r hp hr hl hmul,
    leviJacquetFunctor_preservesColimits p l r hp hr hl hmul⟩

/-- Renard VI.1.2 Corollary: normalized parabolic induction preserves limits and colimits, and
normalized parabolic restriction preserves colimits. -/
theorem leviParabolicFunctorsPreserveLimits :
    LeviParabolicFunctorsPreserveLimitsStatement.{u, v} :=
  leviParabolicFunctorsPreserveLimits_of_quotientCompact arbitraryParabolicQuotientCompact

end Langlands.Aubert.General.RepresentedParabolic
