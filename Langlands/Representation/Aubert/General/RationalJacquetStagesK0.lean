import Langlands.Representation.Aubert.General.RationalJacquetStages
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport

/-! # Exact K0 for rational standard Jacquet restriction in stages -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})

local instance rationalJacquetStagesK0PointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (J : Finset (SimpleRoot i ν)) (I : Finset J)
  (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hWc : Jacquet.Localization.IsLimitOfCompactSubgroups
    ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))
  (hδ :
    (HaarModulus.closedRestrictCharacter (unipotent i ν J) (hU J) (levi i ν J)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J).levi_le_normalizer).comp
        (Subgroup.inclusion
          (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))) *
      standardInnerJacquetModulus i ν hInter hG hi hν hU J I hM =
    HaarModulus.closedRestrictCharacter (unipotent i ν (leviIndex J I))
      (hU (leviIndex J I)) (levi i ν (leviIndex J I))
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex J I)).levi_le_normalizer)
  (hrFl : ∀ A, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν A) (hU A)))
  (hrEx : ∀ A, PreservesFiniteLengthShortExact
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν A) (hU A)))
  (hrLFl : letI := hM.locallyCompactSpace
    PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)))
  (hrLEx : letI := hM.locallyCompactSpace
    PreservesFiniteLengthShortExact
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)))

/-- The actual two-stage Jacquet map on exact finite-length K0, with the
nested endpoint transported to its actual ambient subgroup. -/
def standardIteratedJacquetK0 :
    letI := hM.locallyCompactSpace
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ
        (levi i ν (leviIndex J I)) :=
  letI := hM.locallyCompactSpace
  (FiniteLengthGrothendieckGroup.pullback.{u, u, max (u + 1) v}
      (subgroupOfContinuousEquiv
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))).symm).comp
    ((jacquetK0.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val) hrLFl hrLEx).comp
      (jacquetK0.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J) (hrFl J) (hrEx J)))

include hWc hδ in
/-- Exact finite-length K0 of normalized Jacquet restriction in stages.
The explicit positive Haar-modulus equality is the one in the published
natural-isomorphism interface. -/
theorem standardJacquetK0_stages_of_modulus :
    letI := hM.locallyCompactSpace
    standardIteratedJacquetK0.{u, v}
        i ν hInter hG hi hν hStandard hU J I hM hrFl hrEx hrLFl hrLEx =
      jacquetK0.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν (leviIndex J I))
        (hU (leviIndex J I)) (hrFl (leviIndex J I)) (hrEx (leviIndex J I)) := by
  let _ := hM.locallyCompactSpace
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (RationalPoint k G.X)
  intro A
  simp only [standardIteratedJacquetK0, LinearMap.comp_apply, jacquetK0,
    FiniteLengthGrothendieckGroup.pullback, FiniteLengthGrothendieckGroup.map_ofObject]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((standardJacquetStagesIso.{u, v}
      i ν hInter hG hi hν hStandard hU J I hM hWc hδ).app A.val)

end Langlands.Aubert.General.RationalPointFamily
