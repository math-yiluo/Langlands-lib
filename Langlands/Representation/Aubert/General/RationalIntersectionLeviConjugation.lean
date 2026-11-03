import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Group.RelativeWeylAssociatedIndexing

/-! # Actual Levi transport at the simple intersection indices -/

noncomputable section

open Classical

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]
  {CM : CoxeterMatrix B} (cs : CoxeterSystem CM W) [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
private theorem simple_conjugation_symm_iff (w : W) (a b : B) :
    w * cs.simple a * w⁻¹ = cs.simple b ↔
      w⁻¹ * cs.simple b * w = cs.simple a := by
  constructor <;> intro h <;> rw [← h] <;> group

omit [DecidableEq B] in
private theorem mem_simpleImage_iff (w : W) (I : Finset B) (b : B) :
    b ∈ simpleImage cs w I ↔ ∃ a ∈ I, w * cs.simple a * w⁻¹ = cs.simple b := by
  classical
  simp [simpleImage]

/-- Forward and inverse simple-image intersections use exactly the same
conjugate simple labels, without any root-sign assertion. -/
theorem simpleImage_inv_inter (w : W) (I J : Finset B) :
    simpleImage cs w (simpleImage cs w⁻¹ J ∩ I) = simpleImage cs w I ∩ J := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := (mem_simpleImage_iff cs _ _ _).mp hb
    obtain ⟨c, hc, hca⟩ := (mem_simpleImage_iff cs _ _ _).mp (Finset.mem_inter.mp ha).1
    have hac : w * cs.simple a * w⁻¹ = cs.simple c := by
      exact (simple_conjugation_symm_iff cs w a c).mpr (by simpa using hca)
    have hbc : b = c := simple_reflection_injective cs (hab.symm.trans hac)
    exact Finset.mem_inter.mpr
      ⟨(mem_simpleImage_iff cs _ _ _).mpr ⟨a, (Finset.mem_inter.mp ha).2, hab⟩,
        hbc.symm ▸ hc⟩
  · intro hb
    obtain ⟨a, ha, hab⟩ := (mem_simpleImage_iff cs _ _ _).mp (Finset.mem_inter.mp hb).1
    refine (mem_simpleImage_iff cs _ _ _).mpr ⟨a, Finset.mem_inter.mpr ⟨?_, ha⟩, hab⟩
    exact (mem_simpleImage_iff cs _ _ _).mpr
      ⟨b, (Finset.mem_inter.mp hb).2, by
        simpa using (simple_conjugation_symm_iff cs w a b).mp hab⟩

/-- Every source-intersection label has a simple image in the target one. -/
theorem mapsIntoSimple_intersections (w : W) (I J : Finset B) :
    MapsIntoSimple cs w (simpleImage cs w⁻¹ J ∩ I) (simpleImage cs w I ∩ J) := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := (mem_simpleImage_iff cs _ _ _).mp (Finset.mem_inter.mp ha).1
  have hab : w * cs.simple a * w⁻¹ = cs.simple b :=
    (simple_conjugation_symm_iff cs w a b).mpr (by simpa using hba)
  exact ⟨b, Finset.mem_inter.mpr
    ⟨(mem_simpleImage_iff cs _ _ _).mpr ⟨a, (Finset.mem_inter.mp ha).2, hab⟩, hb⟩, hab⟩

end Langlands.Group.RelativeWeylIndexing

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

universe u

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)

include hLength hSimple in
/-- Minimality makes the source simple images positive, so the intrinsic
intersection indices transport the actual characters without losing signs. -/
theorem rootSet_simpleImage_intersections
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w) :
    weylCharacterAction i hN hZ w '' rootSet i ν (simpleImage cs w⁻¹ J ∩ I) =
      rootSet i ν (simpleImage cs w I ∩ J) := by
  have hpos : ∀ a ∈ simpleImage cs w⁻¹ J ∩ I,
      weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν := by
    intro a ha
    exact (hLength w a).mp
      (((minimalityLengthCriterion_proof cs J I w).mp hw).2 a
        (Finset.mem_inter.mp ha).2)
  have hmap : RootMapsIntoSimple i ν hN hZ w (simpleImage cs w⁻¹ J ∩ I)
      (simpleImage cs w I ∩ J) :=
    (rootMapsIntoSimple_iff_of_positive i ν hN hZ cs hSimple _ _ _ hpos).mpr
      (mapsIntoSimple_intersections cs w I J)
  have hroot := rootSet_rootSimpleImage_of_mapsIntoSimple i ν hN hZ _ _ _ hmap
  rw [rootSimpleImage_eq_simpleImage_of_positive i ν hN hZ cs hSimple _ _ hpos,
    simpleImage_inv_inter] at hroot
  exact hroot.symm

variable [TopologicalSpace (RationalPoint k G.X)]
  [IsTopologicalGroup (RationalPoint k G.X)]

/-- The actual inverse-conjugation equivalence between the standard Levis
at the two simple-intersection indices, for every lift of the minimum. -/
def intersectionLeviConjugationEquiv
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w) :
    levi i ν (simpleImage cs w I ∩ J) ≃ₜ* levi i ν (simpleImage cs w⁻¹ J ∩ I) := by
  have hchar : weylAction i ((normalizerEquiv i hN).symm n) ''
      rootSet i ν (simpleImage cs w⁻¹ J ∩ I) =
        rootSet i ν (simpleImage cs w I ∩ J) := by
    rw [← weylCharacterAction_point_mk i hN hZ, hn]
    exact rootSet_simpleImage_intersections i ν hN hZ cs hLength hSimple I J w hw
  exact conjugationEquiv (n : RationalPoint k G.X)
    (conjugationMembership_of_map_eq _
      (levi_map_conj_of_character_image i ν hG hi hν hConj _ _
        ((normalizerEquiv i hN).symm n) hchar))

@[simp]
theorem intersectionLeviConjugationEquiv_apply
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (x : levi i ν (simpleImage cs w I ∩ J)) :
    (intersectionLeviConjugationEquiv i ν hN hZ cs hLength hSimple hG hi hν hConj
        I J w hw n hn x : RationalPoint k G.X) =
      (n : RationalPoint k G.X)⁻¹ * (x : RationalPoint k G.X) *
        (n : RationalPoint k G.X) := rfl

end Langlands.Aubert.General.RationalPointFamily
