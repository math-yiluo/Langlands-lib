import Langlands.Representation.Aubert.General.RationalInducedJacquetGeometricFiltration
import Langlands.Representation.Aubert.General.RationalLeviCuspidalEmbedding
import Langlands.Representation.CuspidalSupport.RationalLeviSplittingFromWhole
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Proper-standard induction exclusion inside a Levi from the whole-category splitting -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

section Exclusion

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

local instance rationalLeviInductionExclusionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

omit [Mono i.hom.hom.left] in
include hStandard in
/-- Renard VI.5.2 inside every actual standard Levi, for the proper inside-Levi
standard parabolics: the whole-category cuspidal splitting (Renard VI.3.5),
applied to the actual standard Levi scheme, excludes every irreducible
inside-Levi cuspidal representation from proper normalized induction. -/
theorem pointLeviStandardInductionCuspidalExclusion_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u,
      max (u + 1) v}) :
    PointLeviStandardInductionCuspidalExclusion.{u, v} i ν hInter hG hi hν hM hU := by
  intro J K hK
  let := (hM J).locallyCompactSpace
  intro ρ τ hτ hcτ hsub
  have hsplit := hasLeviCuspidalRemainderSplitting_of_wholeStatement.{u, max (u + 1) v}
    hwhole G hG T i hi ν hStandard hInter hν hU J (hM J)
    (Langlands.GroupScheme.relativeRootSystem k _
      (standardLeviScheme_isConnectedReductive i ν hStandard
        Langlands.GroupScheme.dynamicCentralizerReductive hG hi hν J)
      T _
      (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν J)
        (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
        (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))))
    ((normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val)).obj ρ)
  have : τ.representation.IsIrreducible := hτ
  have : Nontrivial τ := by
    have : Nontrivial τ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν J)) _
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : τ.representation.asModule)
    exact nontrivial_of_ne (w₀ : τ) 0 hw₀
  exact no_leviCuspidal_subquotient_of_proper_induction_splitting
    (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) K hK
    (isUnimodularModulus_standardUnipotent_in_levi i ν hG hi hν hStandard hU hM J K)
    ρ hsplit τ this hsub hcτ

end Exclusion

/-- Renard VI.3.5 (the whole-category cuspidal splitting, at the carrier
universe `max (u + 1) v`) proves both inputs of the actual extraction route:
the geometric filtration is unconditional and the proper-standard exclusion
follows from the splitting. -/
theorem rationalCuspidalExtractionInputs_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u,
      max (u + 1) v}) :
    RationalCuspidalExtractionInputsStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact ⟨exists_pointInducedJacquetGeometricFiltration.{u, v}
      i ν hN hZ hStandard hInter hRoots hG hi hν hM hU,
    pointLeviStandardInductionCuspidalExclusion_of_wholeStatement.{u, v}
      i ν hStandard hInter hG hi hν hM hU hwhole⟩

end Langlands.Aubert.General.RationalPointFamily
