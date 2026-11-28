import Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalInductionBoundsStatement
import Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalHomBoundFamily
import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionLengthBound
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.Group.RelativeWeylMinimalUniqueProof

/-! # Numerical bounds for induction from supercuspidal representations (Renard VI.5.4) -/

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe uF uV

namespace Langlands.CuspidalSupport

open _root_.CategoryTheory _root_.AlgebraicGeometry GroupScheme Group.RelativeWeylIndexing
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

local instance boundsAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance boundsAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

section MatchingCosets

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Distinct matching minimal double-coset representatives lie in distinct
source-Levi cosets `w W_M`. -/
private theorem card_minimal_matching_le_card_cosets [Finite (Weyl i)]
    {C : CoxeterMatrix (SimpleRoot i ν)} (cs : ActualCoxeterSystem (torusPoints i) C)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (a a' : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    Nat.card {w : Weyl i // IsMinimal cs a'.roots a.roots w ∧
        w ∈ HomBound.bernsteinMatchingWeyl i ν family a a'} ≤
      Nat.card ((QuotientGroup.mk : Weyl i → Weyl i ⧸
          (Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν a.roots)).range) ''
        HomBound.bernsteinMatchingWeyl i ν family a a') := by
  refine Nat.card_le_card_of_injective
    (fun w => ⟨QuotientGroup.mk w.1, w.1, w.2.2, rfl⟩) ?_
  intro w w' hw
  have heq : (QuotientGroup.mk w.1 : Weyl i ⧸
      (Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν a.roots)).range) =
      QuotientGroup.mk w'.1 := congrArg Subtype.val hw
  rw [QuotientGroup.eq, hIdent a.roots] at heq
  have hmember : w'.1 ∈ doubleCoset cs a'.roots a.roots w.1 :=
    ⟨1, (standardSubgroup cs a'.roots).one_mem, w.1⁻¹ * w'.1, heq, by simp⟩
  exact Subtype.ext (minimalRepresentativeUnique_proof cs a'.roots a.roots w.1 w.1 w'.1
    (mem_doubleCoset_self cs a'.roots a.roots w.1) hmember w.2.1 w'.2.1)

end MatchingCosets

local instance boundsLeviClosedImmersion (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance boundsLeviAffine (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance boundsLeviTopology (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

/-- Renard VI.5.4 gives the length and intertwiner-rank bounds for induction
from standard cuspidal data. -/
theorem bernsteinSupercuspidalInductionBounds :
    BernsteinSupercuspidalInductionBoundsStatement.{uF, uV} := by
  have hInputs : RationalCuspidalExtractionInputsStatement.{uF, uV} :=
    rationalCuspidalExtractionInputs_of_specialVertexInputs
      (rationalSpecialVertexCompactInputs_of_jointBasis
        BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence)
  intro F _ _ _ _ G _ _ T i ν _ _ family WL
  have hG := family.connectedReductive
  have hi := family.maximalSplitTorus
  have hν := family.genericCocharacter
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  have hRoots : HasRelativeRootSystem i := relativeRootSystem F G hG T i hi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  obtain ⟨hN, hZ⟩ := rationalWeylComparison F G hG T i hi
  obtain ⟨hW, -, C, cs, hLength, -, hIdent⟩ :=
    exists_rootSpanPointCoxeterSystem i ν hN hZ hG hi hRoots hν
  let : Fintype (Weyl i) := Fintype.ofFinite _
  refine ⟨fun a => ?_, fun a a' => ?_⟩
  · have hdet := rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors
      (rationalCuspidalJacquetFactorExtraction_of_inputs hInputs)
    have hρ : (bernsteinLiteralLeviRep i ν a.roots a.representation).IsIrreducible :=
      (isIrreducible_comp_continuousMulEquiv_iff a.representation.representation
        (leviRationalPointHomeomorph i ν a.roots).symm).mpr a.irreducible
    exact pointSupercuspidalInduction_compositionLengthAtMost_sourceCosets
      i ν hN hZ cs hIdent hLength standardCocharacter standardLeviIntersection hRoots
      hG hi hν family.closedLevi family.closedUnipotent hdet a.roots
      (bernsteinLiteralLeviRep i ν a.roots a.representation) hρ a.cuspidal
  · exact (HomBound.bernsteinInduction_rank_intertwiningMap_le_card_minimal_of_inputs
      i ν family hInputs hN hZ cs hIdent hLength a a').trans
      (Nat.cast_le.mpr (card_minimal_matching_le_card_cosets i ν family cs hIdent a a'))

end Langlands.CuspidalSupport
