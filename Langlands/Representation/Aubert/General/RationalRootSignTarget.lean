import Langlands.Representation.Aubert.General.RationalWeylRootAction
import Langlands.Group.RelativeWeylIndexingTargets

/-!
# Actual root-sign comparisons for the relative Coxeter indexing

The indices are actual simple characters and the group is the actual
normalizer/full-centralizer quotient. The comparison propositions remain
unproved; their elementary set-theoretic consequences are proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- The actual simple characters whose images are positive relative roots. -/
def rootPositiveSimpleSet [Fintype (SimpleRoot i ν)] (w : Weyl i) :
    Finset (SimpleRoot i ν) := by
  classical
  exact Finset.univ.filter (fun a =>
    weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν)

@[simp] theorem mem_rootPositiveSimpleSet [Fintype (SimpleRoot i ν)]
    (w : Weyl i) (a : SimpleRoot i ν) :
    a ∈ rootPositiveSimpleSet i ν hN hZ w ↔
      weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν := by
  classical
  simp [rootPositiveSimpleSet]

/-- Only actual positive simple-root images are retained. Equality of
characters distinguishes a root from its negative. -/
def rootSimpleImage [Fintype (SimpleRoot i ν)]
    (w : Weyl i) (I : Finset (SimpleRoot i ν)) :
    Finset (SimpleRoot i ν) := by
  classical
  exact Finset.univ.filter (fun b =>
    ∃ a ∈ I, weylCharacterAction i hN hZ w a.val = b.val)

@[simp] theorem mem_rootSimpleImage [Fintype (SimpleRoot i ν)]
    (w : Weyl i) (I : Finset (SimpleRoot i ν)) (b : SimpleRoot i ν) :
    b ∈ rootSimpleImage i ν hN hZ w I ↔
      ∃ a ∈ I, weylCharacterAction i hN hZ w a.val = b.val := by
  classical
  simp [rootSimpleImage]

/-- Every root image is accounted for in the specified target subset. -/
def RootMapsIntoSimple (w : Weyl i) (I J : Finset (SimpleRoot i ν)) : Prop :=
  ∀ a ∈ I, ∃ b ∈ J, weylCharacterAction i hN hZ w a.val = b.val

theorem rootSet_rootSimpleImage [Fintype (SimpleRoot i ν)]
    (w : Weyl i) (I : Finset (SimpleRoot i ν)) :
    rootSet i ν (rootSimpleImage i ν hN hZ w I) =
      weylCharacterAction i hN hZ w '' rootSet i ν I ∩ simpleRelativeRoots i ν := by
  ext α
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases (mem_rootSimpleImage i ν hN hZ w I b).mp hb with ⟨a, ha, hab⟩
    exact ⟨⟨a.val, ⟨a, ha, rfl⟩, hab⟩, b.property⟩
  · rintro ⟨⟨β, ⟨a, ha, rfl⟩, hα⟩, hs⟩
    exact ⟨⟨α, hs⟩,
      (mem_rootSimpleImage i ν hN hZ w I ⟨α, hs⟩).mpr ⟨a, ha, hα⟩, rfl⟩

theorem rootSet_rootSimpleImage_of_mapsIntoSimple
    [Fintype (SimpleRoot i ν)]
    (w : Weyl i) (I J : Finset (SimpleRoot i ν))
    (h : RootMapsIntoSimple i ν hN hZ w I J) :
    rootSet i ν (rootSimpleImage i ν hN hZ w I) =
      weylCharacterAction i hN hZ w '' rootSet i ν I := by
  rw [rootSet_rootSimpleImage]
  apply Set.inter_eq_left.mpr
  rintro α ⟨β, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨b, _, hab⟩ := h a ha
  rw [hab]
  exact b.property

variable {M : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) M)

/-- Right length increases exactly when the actual simple character has
positive image, with the source's convention for the Weyl action. -/
def RootLengthComparison : Prop :=
  ∀ (w : Weyl i) (a : SimpleRoot i ν),
    cs.length w < cs.length (w * cs.simple a) ↔
      weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν

/-- Reflection-label conjugacy detects the same actual simple character
when its image is positive. The positivity premise is essential. -/
def PositiveSimpleReflectionComparison : Prop :=
  ∀ (w : Weyl i) (a b : SimpleRoot i ν),
    weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν →
      (w * cs.simple a * w⁻¹ = cs.simple b ↔
        weylCharacterAction i hN hZ w a.val = b.val)

theorem positiveSimpleSet_eq_rootPositiveSimpleSet [Fintype (SimpleRoot i ν)]
    (h : RootLengthComparison i ν hN hZ cs) (w : Weyl i) :
    positiveSimpleSet cs w = rootPositiveSimpleSet i ν hN hZ w := by
  classical
  ext a
  simpa only [positiveSimpleSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_rootPositiveSimpleSet] using h w a

theorem rootSimpleImage_eq_simpleImage_of_positive [Fintype (SimpleRoot i ν)]
    (h : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (w : Weyl i) (I : Finset (SimpleRoot i ν))
    (hI : ∀ a ∈ I,
      weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν) :
    rootSimpleImage i ν hN hZ w I = simpleImage cs w I := by
  classical
  ext b
  simp only [mem_rootSimpleImage, simpleImage, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hab⟩
    exact ⟨a, ha, (h w a b (hI a ha)).mpr hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨a, ha, (h w a b (hI a ha)).mp hab⟩

theorem rootMapsIntoSimple_iff_of_positive
    (h : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (w : Weyl i) (I J : Finset (SimpleRoot i ν))
    (hI : ∀ a ∈ I,
      weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν) :
    RootMapsIntoSimple i ν hN hZ w I J ↔ MapsIntoSimple cs w I J := by
  constructor
  · intro hmap a ha
    obtain ⟨b, hb, hab⟩ := hmap a ha
    exact ⟨b, hb, (h w a b (hI a ha)).mpr hab⟩
  · intro hmap a ha
    obtain ⟨b, hb, hab⟩ := hmap a ha
    exact ⟨b, hb, (h w a b (hI a ha)).mp hab⟩

/-- Under the separately named intrinsic and root-sign assertions, the
associated subset is literally the inverse longest representative's root image. -/
theorem rootSet_associatedSubset [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
    (J : Finset (SimpleRoot i ν)) :
    rootSet i ν (associatedSubset cs J) =
      weylCharacterAction i hN hZ (longestRep cs J)⁻¹ '' rootSet i ν J := by
  have hmin : IsMinimal cs ∅ J (longestRep cs J)⁻¹ :=
    isMinimal_inv cs ((mem_minimalReps cs J ∅ _).mp (longestRep_mem cs J))
  have hpos : ∀ a ∈ J, weylCharacterAction i hN hZ (longestRep cs J)⁻¹ a.val ∈
      positiveRelativeRoots i ν := by
    intro a ha
    exact (hLength _ a).mp (((hMin ∅ J _).mp hmin).2 a ha)
  have hmap : RootMapsIntoSimple i ν hN hZ (longestRep cs J)⁻¹ J Finset.univ :=
    (rootMapsIntoSimple_iff_of_positive i ν hN hZ cs hSimple _ J Finset.univ
      hpos).mpr (hAssoc J).1
  change rootSet i ν (simpleImage cs (longestRep cs J)⁻¹ J) = _
  rw [← rootSimpleImage_eq_simpleImage_of_positive i ν hN hZ cs hSimple _ J hpos]
  exact rootSet_rootSimpleImage_of_mapsIntoSimple i ν hN hZ _ J Finset.univ hmap

/-- Existence of a Coxeter system on the actual quotient, with its labels
fixed to the actual simple roots and both root-sign comparisons explicit. -/
def HasRootSignCoxeterRealization : Prop :=
  ∃ (M : CoxeterMatrix (SimpleRoot i ν))
    (actual : ActualCoxeterSystem (torusPoints i) M),
      RootLengthComparison i ν hN hZ actual ∧
        PositiveSimpleReflectionComparison i ν hN hZ actual

/-- The unproved root-sign realization target at connected-reductive
nonarchimedean local-field scope. The two point comparisons remain separate. -/
def RationalRootSignCoxeterStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i),
        HasRootSignCoxeterRealization i ν hN hZ

end Langlands.Aubert.General.RationalPointFamily
