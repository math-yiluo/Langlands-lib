import Langlands.Representation.Jacquet.IwahoriJacquetNonvanishing
import Langlands.Representation.Jacquet.BernsteinFixedVectorSplitting
import Langlands.Representation.Jacquet.IrreducibleFixedVectorGeneration
import Langlands.Representation.CuspidalSupport.BernsteinSupportJacquetPresentation
import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # Fixed-vector visibility of Bernstein classes from support uniqueness and the
standard-representative criterion -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.CuspidalSupport
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.Jacquet

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardIwahoriVisibilityAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardIwahoriVisibilityTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν) (K : OpenSubgroup (rationalPoints G))

/-- One direction of fixed-vector visibility: if two irreducibles have the same inertial
support and the first has a nonzero `K`-fixed vector, so does the second. Inputs: uniqueness
of inertial support, the direction (⇒) of the standard-representative criterion, standard
cocharacters, and Iwahori decompositions of `K` along every standard parabolic. -/
theorem nontrivial_fixedVectors_of_sameInertialSupport
    (hstd : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
      HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
    (huniq : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (hcrit : ∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ∧
            Nontrivial (fixedVectors π.representation K.toSubgroup)) →
        Nontrivial (fixedVectors
          (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
          (K.toSubgroup.comap (levi i ν a.roots).subtype)))
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (π τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : IsBernsteinInertialSupport i ν family s π)
    (hτ : IsBernsteinInertialSupport i ν family s τ)
    (hπK : Nontrivial (fixedVectors π.representation K.toSubgroup)) :
    Nontrivial (fixedVectors τ.representation K.toSubgroup) := by
  have hτirr : τ.IsIrreducible := by
    obtain ⟨_, _, h⟩ := hτ
    exact h.1
  obtain ⟨c, hcq, hcsub⟩ :=
    exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding i ν family τ hτirr
  have hcs : bernsteinInertialClass i ν family c = s :=
    huniq τ _ _ (IsBernsteinCuspidalSupport.inertial ⟨hτirr, hcsub.isSubquotient⟩) hτ
  have hσ := hcrit c ⟨π, hcs ▸ hπ, hπK⟩
  let M := levi i ν c.roots
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    (family.closedLevi c.roots).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hJac := SmoothRep.nontrivial_fixedVectors_of_isSubquotient KM hKM hcq.isSubquotient hσ
  have hJ := rootSet_subset i ν c.roots
  exact nontrivial_fixedVectors_of_standardNormalizedJacquet i ν family.connectedReductive
    family.maximalSplitTorus family.genericCocharacter hJ (hstd _ hJ) K hK (hIwahori _ hJ)
    (family.closedUnipotent c.roots) (family.closedLevi c.roots)
    (family.decomposition c.roots).levi_le_normalizer τ hJac

/-- Fixed-vector visibility of Bernstein classes at a level `K` with Iwahori decompositions,
from uniqueness of inertial support and the direction (⇒) of the standard-representative
criterion. -/
theorem bernsteinFixedVectorVisibility_of_uniqueness_of_necessity
    (hstd : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
      HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
        (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
    (huniq : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (hcrit : ∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ∧
            Nontrivial (fixedVectors π.representation K.toSubgroup)) →
        Nontrivial (fixedVectors
          (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
          (K.toSubgroup.comap (levi i ν a.roots).subtype))) :
    bernsteinFixedVectorVisibility.{uF, uV} i ν family K := by
  intro s π τ hπ hτ
  exact ⟨nontrivial_fixedVectors_of_sameInertialSupport i ν family K hstd hK hIwahori huniq
      hcrit s π τ hπ hτ,
    nontrivial_fixedVectors_of_sameInertialSupport i ν family K hstd hK hIwahori huniq
      hcrit s τ π hτ hπ⟩

end Langlands.Jacquet
