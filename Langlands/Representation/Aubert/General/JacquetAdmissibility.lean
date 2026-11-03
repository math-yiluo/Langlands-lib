import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-!
# Admissibility of the general normalized Jacquet functor

The actual normalized Jacquet functor of `Aubert.General.Parabolic` preserves
admissibility whenever compact open subgroups with abstract Iwahori factorization
and contraction data have arbitrarily small Levi parts.
-/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- The actual normalized Jacquet functor preserves admissibility when compact
open subgroups with abstract Iwahori factorization and contraction have
arbitrarily small Levi parts. -/
theorem isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction
    (U M Ubar : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hbasis : Jacquet.HasIwahoriContractionBasis U M Ubar)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible) :
    ((normalizedJacquetFunctor U M hU hMU).obj A).IsAdmissible := by
  change Langlands.IsAdmissible (Langlands.twist
    (HaarModulus.closedInverseHalfCharacter U hU M hMU)
    (Jacquet.Localization.action A.representation U 1 M hMU
      (Jacquet.Localization.isInvariant_one U M hMU)))
  rw [Langlands.isAdmissible_twist_iff _ _
    (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M hMU),
    Langlands.isAdmissible_iff_of_equiv
      (Jacquet.Localization.trivialEquiv A.representation U M hMU)]
  exact Jacquet.isAdmissible_action_of_iwahoriContraction A.representation hA U M Ubar hMU
    hbasis

/-- The same statement for the Jacquet functor of a semidirect decomposition
`P = M ⋉ U`, as used by the general finite-length targets. -/
theorem isAdmissible_jacquetFunctor_obj_of_iwahoriContraction {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G)) (Ubar : Subgroup G)
    (hbasis : Jacquet.HasIwahoriContractionBasis U M Ubar)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible) :
    ((jacquetFunctor h hU).obj A).IsAdmissible :=
  isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction U M Ubar hU
    h.levi_le_normalizer hbasis A hA

end Langlands.Aubert.General
