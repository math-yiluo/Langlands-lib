import Langlands.Group.ActualRelativeWeylTransporterCosets
import Langlands.Group.RelativeWeylCoatomSurvivors
import Langlands.Representation.Aubert.General.MaximalRootAssociationClasses
import Langlands.Representation.Aubert.General.RankOneLongestLiftNormalization
import Langlands.Representation.Aubert.General.RationalSupportAssociation

/-! # Full-intersection pairs and the actual standard-Levi source-coset budget -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open Classical GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

/-- The literal Weyl transporter set to all standard Levis, with the source
fixed. This is the set used in the length bound of Renard VI.5.4. -/
def standardLeviTransportingWeyl (I : Finset (SimpleRoot i ν)) : Set (Weyl i) :=
  {w | ∃ (J : Finset (SimpleRoot i ν))
      (n : Group.RelativeWeyl.normalizer (torusPoints i)),
    (QuotientGroup.mk n : Weyl i) = w ∧
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) : _ →* _) = levi i ν J}

/-- Source-Levi Weyl cosets meeting the literal transporter set. -/
def standardLeviTransporterSourceCosets (I : Finset (SimpleRoot i ν)) :
    Set (Weyl i ⧸ (Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν I)).range) :=
  QuotientGroup.mk '' standardLeviTransportingWeyl i ν I

theorem actualTransporterSourceCosets_true (I : Finset (SimpleRoot i ν)) :
    actualTransporterSourceCosets (torusPoints i) (levi i ν) I
      (fun _ _ _ => True) = standardLeviTransporterSourceCosets i ν I := by
  ext c
  constructor
  · rintro ⟨w, ⟨J, n, h, hn, _⟩, rfl⟩
    exact ⟨w, ⟨J, n, hn, h⟩, rfl⟩
  · rintro ⟨w, ⟨J, n, hn, h⟩, rfl⟩
    exact ⟨w, ⟨J, n, h, hn, trivial⟩, rfl⟩

variable [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})

include hLength hSimple hG hi hν hStandard in
/-- Every equal-rank minimal pair with full source intersection has an actual
normalizer lift carrying the literal source Levi onto the literal target. -/
theorem fullIntersectionPair_actualTransporter
    (I : Finset (SimpleRoot i ν))
    (p : fullIntersectionPairs cs I) :
    actualTransporterSelection (torusPoints i) (levi i ν) I
      (fun _ _ _ => True) p.val.1 p.val.2 := by
  have hp : p.val.1.card = I.card ∧ IsMinimal cs p.val.1 I p.val.2 ∧
      intersectionSubset cs p.val.1 I p.val.2 = I := by
    simpa only [fullIntersectionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      using p.property
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective p.val.2
  have hA : rootAssociation i ν hN hZ I p.val.1 (n : RationalPoint k G.X) := by
    refine ⟨n.property, ?_⟩
    change weylCharacterAction i hN hZ (QuotientGroup.mk n) '' rootSet i ν I = _
    rw [hn]
    exact rootImage_eq_of_full_intersection i ν hN hZ cs hLength hSimple
      (minimalityLengthCriterion_proof cs) hp.2.1 hp.2.2 hp.1.symm
  exact ⟨n, levi_map_conj_of_rootAssociation i ν hG hi hν hStandard hN hZ
    I p.val.1 n hA, hn, trivial⟩

/-- Preserve the original target and Weyl representative when viewing
full-intersection pairs as actual minimal transporters. -/
def fullIntersectionPairTransporterEmbedding (I : Finset (SimpleRoot i ν)) :
    fullIntersectionPairs cs I ↪
      actualMinimalTransporterPairs (torusPoints i) (levi i ν) cs I
        (fun _ _ _ => True) where
  toFun p := ⟨p.val, by
    constructor
    · have hp := p.property
      simp only [fullIntersectionPairs, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      exact hp.2.1
    · exact fullIntersectionPair_actualTransporter i ν hN hZ cs hLength hSimple
        hG hi hν hStandard I p⟩
  inj' _ _ h := Subtype.ext (congrArg
    (fun p : actualMinimalTransporterPairs (torusPoints i) (levi i ν) cs I
      (fun _ _ _ => True) => p.val) h)

include hLength hSimple hG hi hν hStandard in
/-- The whole equal-rank full-intersection budget is bounded by the exact
actual source-Levi coset image appearing in the length theorem. -/
theorem card_fullIntersectionPairs_le_sourceCosets
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (I : Finset (SimpleRoot i ν)) :
    (fullIntersectionPairs cs I).card ≤
      Nat.card (standardLeviTransporterSourceCosets i ν I) := by
  have hZL : ∀ J, Group.RelativeWeyl.centralizer (torusPoints i) ≤ levi i ν J := by
    intro J
    rw [← hZ]
    exact centralizerPoints_le_levi i ν J
  have hL := leviFamily_injective_of_actualLeviWeylIdentification
    (levi i ν) (torusPoints i) cs hIdent
  calc
    _ = Nat.card (fullIntersectionPairs cs I) := (Nat.card_eq_finsetCard _).symm
    _ ≤ Nat.card (actualMinimalTransporterPairs (torusPoints i) (levi i ν) cs I
        (fun _ _ _ => True)) :=
      Nat.card_le_card_of_injective
        (fullIntersectionPairTransporterEmbedding i ν hN hZ cs hLength hSimple
          hG hi hν hStandard I)
        (fullIntersectionPairTransporterEmbedding i ν hN hZ cs hLength hSimple
          hG hi hν hStandard I).injective
    _ ≤ Nat.card (actualTransporterSourceCosets (torusPoints i) (levi i ν) I
        (fun _ _ _ => True)) :=
      card_actualMinimalTransporterPairs_le (torusPoints i) (levi i ν) cs I
        (fun _ _ _ => True) hZL hL hIdent
    _ = _ := by rw [actualTransporterSourceCosets_true]

end Langlands.Aubert.General.RationalPointFamily
