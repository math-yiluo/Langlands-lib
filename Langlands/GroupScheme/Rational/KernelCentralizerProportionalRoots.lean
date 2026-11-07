import Langlands.GroupScheme.Rational.KernelCentralizerWeightSupport
import Langlands.GroupScheme.Reductive.RankOneCentralizerDetection
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Reductive.FiniteCentralizerNeighbourhood
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Proportional-root centralizers inside full character-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

/-- Homomorphisms preserve full character-kernel centralization on all tests. -/
theorem map_mem_kernelCentralizer
    {B : Scheme.{u}} {S : CommGroupScheme B} {M G : GroupScheme B}
    (q : M ⟶ G) (i : S.toGrp ⟶ M) (a : characterLattice S)
    {V : Over B} {x : V ⟶ M.X} (hx : x ∈ (kernelCentralizer i a).carrier V) :
    x ≫ q.hom.hom ∈ (kernelCentralizer (i ≫ q) a).carrier V := by
  rw [mem_kernelCentralizer] at hx ⊢
  intro W b c
  apply (commute_iff_eq _ _).mpr
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp] using
    congrArg (fun y : W ⟶ M.X => y ≫ q.hom.hom) (hx W b c).eq

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- In the generic proportional-root centralizer, every root is the chosen
ambient root or its negative. -/
theorem root_eq_or_neg_of_proportionalCentralizer
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    {α : characterLattice T} (hα : α ∈ roots i)
    {β : characterLattice T}
    (hβ : β ∈ roots (RankOneCentralizerDetection.torusHom i hT α hα.1)) :
    β = α ∨ β = -α := by
  obtain ⟨hβG, hβζ⟩ := RootReducedness.mem_roots_of_mem_roots_torusFactor i
    (RankOneCentralizerDetection.cocharacter i hT α hα.1)
    (RankOneCentralizerDetection.isRepresentedBy_inclusion i hT α hα.1) hβ
  have hdep := RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
    hT hα.1 (hT.finite_relativeRoots i) hβG hβζ
  rcases rootReducedness k G hG T hT i hi α hα β hβG hdep with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

/-- If the chosen ambient root restricts to an integer multiple of `a`, the
entire actual proportional-root centralizer centralizes the full kernel of `a`.
This statement concerns all scheme tests, including nonreduced tests. -/
theorem range_proportionalCentralizer_le_kernelCentralizer
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
    (a : characterLattice S) (ha : a ≠ 0)
    {α : characterLattice T} (hα : α ∈ roots i)
    (hres : f ≫ α ∈ AddSubgroup.zmultiples a) :
    SubgroupFunctor.range (RankOneCentralizerDetection.inclusion i hT α hα.1) ≤
      kernelCentralizer (CommGroupScheme.groupHom f ≫ i) a := by
  let L := RankOneCentralizerDetection.groupScheme i hT α hα.1
  let q : L ⟶ G := RankOneCentralizerDetection.inclusion i hT α hα.1
  let t : T.toGrp ⟶ L := RankOneCentralizerDetection.torusHom i hT α hα.1
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hroot : ∀ β ∈ roots t, f ≫ β ∈ AddSubgroup.zmultiples a := by
    intro β hβ
    rcases root_eq_or_neg_of_proportionalCentralizer hG i hT hi hα hβ with h | h
    · rwa [h]
    · simpa only [h, Preadditive.comp_neg] using (AddSubgroup.neg_mem _ hres)
  have hspan := integralWeightSpan_eq_top_of_root_restrictions hT f t a hroot
  have hcent := kernelCentralizer_eq_top_of_integralWeightSpan_eq_top hS
    (CommGroupScheme.groupHom f ≫ t) a ha hspan
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ∈ (kernelCentralizer (CommGroupScheme.groupHom f ≫ t) a).carrier V := by
    rw [hcent]
    trivial
  have hm := map_mem_kernelCentralizer q (CommGroupScheme.groupHom f ≫ t) a hy
  simpa only [Category.assoc, RankOneCentralizerDetection.torusHom_comp, t, q] using hm

/-- The canonical ambient proportional-root centralizer, equipped with its
actual representation, annihilating cocharacter and trivial radical. -/
def proportionalRootCentralizerData
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (α : characterLattice T) (hα : α ≠ 0) :
    RadicalFreeRootCentralizerData i α where
  cocharacter := RankOneCentralizerDetection.cocharacter i hT α hα
  groupScheme := RankOneCentralizerDetection.groupScheme i hT α hα
  inclusion := RankOneCentralizerDetection.inclusion i hT α hα
  represents := RankOneCentralizerDetection.isRepresentedBy_inclusion i hT α hα
  annihilates := RankOneCentralizerDetection.pairing_cocharacter i hT α hα
  radical := (dynamicCentralizerReductive k G hG _ _ _
    (RankOneCentralizerDetection.isClosedSubgroup_inclusion i hT α hα)
    (RankOneCentralizerDetection.isRepresentedBy_inclusion i hT α hα)).hasTrivialUnipotentRadical

end Langlands.GroupScheme.RelativeRoot
