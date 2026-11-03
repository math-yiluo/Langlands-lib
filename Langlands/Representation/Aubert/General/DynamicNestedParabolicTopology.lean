import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.Representation.Aubert.General.DynamicNestedParabolicTransitivityStatement
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.BruhatTits.Unipotent.JacquetCompactContainmentProof
import Langlands.Representation.Aubert.General.SemidirectHaarModulus
import Langlands.Representation.Aubert.General.Conjugation
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section

universe u
open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

/-- Local fields are second countable in their given valuative topology. -/
theorem localField_secondCountableTopology (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : SecondCountableTopology F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.secondCountableTopology F

/-- Finite-type affine rational points inherit second countability from the field. -/
theorem rationalPoint_secondCountableTopology
    (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [SecondCountableTopology F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] :
    let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    SecondCountableTopology (RationalPoint F G.X) := by
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  have hA : Algebra.FiniteType F (AffineCoordinateRing F G.X) := inferInstance
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have he := ((AlgPoint.polynomialPointHomeomorph (R := F) (S := F) (Fin n)).isEmbedding.comp
    (AlgPoint.isEmbedding_precomp_of_surjective f hf)).comp
      ((affineSchemePointHomeomorph F G.X F).isEmbedding.comp
        (rationalPointHomeomorph F G.X).isEmbedding)
  exact he.secondCountableTopology


/-- Compact-subgroup containment pulls back through a closed embedding. -/
theorem compactLimit_of_closedEmbedding
    {A B : Type*} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (V : Subgroup A) (U : Subgroup B) (f : V →* U)
    (hf : IsClosedEmbedding f)
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    Jacquet.Localization.IsLimitOfCompactSubgroups V := by
  intro C hC
  obtain ⟨K, hK, hCK⟩ := hU (f '' C) (hC.image hf.continuous)
  exact ⟨K.comap f, hf.isProperMap.isCompact_preimage hK,
    fun x hx => hCK ⟨x, hx, rfl⟩⟩

/-- The actual inclusion of the subgroup copy in its original subgroup. -/
abbrev subgroupOfToOriginal
    {A : Type*} [Group A] (N L : Subgroup A) : N.subgroupOf L →* N :=
  subgroupOfToAmbient N L

/-- Intersecting with a closed subgroup preserves compact-subgroup containment,
including the literal subgroup copy inside that closed subgroup. -/
theorem compactLimit_subgroupOf
    {A : Type*} [Group A] [TopologicalSpace A]
    (N L : Subgroup A) (hL : IsClosed (L : Set A))
    (hN : Jacquet.Localization.IsLimitOfCompactSubgroups N) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (N.subgroupOf L) :=
  isLimitOfCompactSubgroups_subgroupOf N L hL hN

end Langlands.Aubert.General
