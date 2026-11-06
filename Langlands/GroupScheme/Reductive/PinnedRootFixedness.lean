import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Reductive.RootTorusGeneration
import Langlands.GroupScheme.Rational.RootSubgroupFixedByEndomorphism
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Rigidity from fixed simple root subgroups and actual opposite pairs -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Every indexed root of the actual pinned datum is an actual relative root. -/
theorem root_mem_relativeRoots (a : p.rootIndex) :
    p.rootDatum.root a ∈ relativeRoots p.inclusion := by
  rw [relativeRoots_eq_roots, ← p.isRootDatum.2.1]
  exact Set.mem_range_self a

/-- The normalizer of a supplied opposite pair acts by the reflection of the
supplied pinned root datum on the entire integral character lattice. -/
theorem oppositeFactorPair_weylAction (a : p.rootIndex)
    {x : rationalPoints G} {q : rationalPoints G × rationalPoints G}
    (hx : x ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier
      (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root a) x q) :
    haveI : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
    weylAction p.inclusion (⟨q.1 * x * q.2, hq.2.2⟩ : normalizerPoints p.inclusion) =
      p.rootDatum.reflection a := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  let : Finite (weylImage p.inclusion) := splitTorusWeylImageFinite k G
    p.torus p.isSplitTorus p.inclusion p.isMaximalTorus.2.1
  let n : normalizerPoints p.inclusion := ⟨q.1 * x * q.2, hq.2.2⟩
  obtain ⟨m, hm⟩ := p.isRootDatum.exists_reflectionRepresentative a
  let s : weylImage p.inclusion := ⟨weylAction p.inclusion n, n, rfl⟩
  let t : weylImage p.inclusion := ⟨p.rootDatum.reflection a, m, hm⟩
  have horder : IsOfFinOrder (weylAction p.inclusion n * p.rootDatum.reflection a) :=
    (weylImage p.inclusion).subtype.isOfFinOrder (isOfFinOrder_of_finite (s * t))
  let c := hq.coroot p.inclusion p.isSplitTorus (p.root_mem_relativeRoots a).1 hx hx1
  let F := (latticePairing p.torus).flip c
  let K := (latticePairing p.torus).flip (p.rootDatum.coroot a)
  have hspec := hq.coroot_spec p.inclusion p.isSplitTorus
    (p.root_mem_relativeRoots a).1 hx hx1
  have hF : F (p.rootDatum.root a) = 2 := hspec.1
  have hK : K (p.rootDatum.root a) = 2 := by
    change latticePairing p.torus (p.rootDatum.root a) (p.rootDatum.coroot a) = 2
    rw [← p.isRootDatum.1]
    exact p.rootDatum.root_coroot_two a
  have hfun := Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections
    (p.rootDatum.root a) F K (weylAction p.inclusion n) (p.rootDatum.reflection a)
    hF hK hspec.2 (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - p.rootDatum.toLinearMap χ (p.rootDatum.coroot a) • p.rootDatum.root a = _
      rw [p.isRootDatum.1]
      rfl) horder
  ext χ
  rw [hspec.2, RootPairing.reflection_apply]
  change χ - F χ • p.rootDatum.root a =
    χ - p.rootDatum.toLinearMap χ (p.rootDatum.coroot a) • p.rootDatum.root a
  rw [p.isRootDatum.1, LinearMap.congr_fun hfun χ]
  rfl

/-- A fixed actual root supplies a fixed normalizer representing its specified
root-datum reflection, assuming actual opposite-pair existence. -/
theorem exists_fixed_reflectionNormalizer
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion) (f : G ⟶ G)
    (hi : p.inclusion ≫ f = p.inclusion) (a : p.rootIndex)
    (hfix : RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a)) :
    haveI : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
    ∃ n : normalizerPoints p.inclusion,
      n.val ≫ f.hom.hom = n.val ∧ weylAction p.inclusion n = p.rootDatum.reflection a := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual p.isSplitTorus
    p.inclusion (p.root_mem_relativeRoots a)
  obtain ⟨q, hq⟩ := hE _ (p.root_mem_relativeRoots a) x hx hx1
  refine ⟨⟨q.1 * x * q.2, hq.2.2⟩, ?_, p.oppositeFactorPair_weylAction a hx hx1 hq⟩
  exact hq.normalizer_fixed_of_fixed p.inclusion p.isSplitTorus f hi
    (p.root_mem_relativeRoots a).1 hx hx1 (hfix _ hx)

/-- Choose the actual fixed normalizer provided by a fixed root and pair existence. -/
def fixedReflectionNormalizer
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion) (f : G ⟶ G)
    (hi : p.inclusion ≫ f = p.inclusion) (a : p.rootIndex)
    (hfix : RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a)) :
    haveI : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
    normalizerPoints p.inclusion :=
  Classical.choose (p.exists_fixed_reflectionNormalizer hE f hi a hfix)

/-- The chosen normalizer is fixed and induces the exact pinned reflection. -/
theorem fixedReflectionNormalizer_spec
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion) (f : G ⟶ G)
    (hi : p.inclusion ≫ f = p.inclusion) (a : p.rootIndex)
    (hfix : RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a)) :
    haveI : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
    let n := p.fixedReflectionNormalizer hE f hi a hfix
    n.val ≫ f.hom.hom = n.val ∧ weylAction p.inclusion n = p.rootDatum.reflection a :=
  Classical.choose_spec (p.exists_fixed_reflectionNormalizer hE f hi a hfix)

/-- Fixedness propagates through any reflection whose root is fixed. -/
theorem root_fixed_reflection
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion) (f : G ⟶ G)
    (hi : p.inclusion ≫ f = p.inclusion) (a b : p.rootIndex)
    (ha : RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a))
    (hb : RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root b)) :
    RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root (p.rootDatum.reflectionPerm a b)) := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  obtain ⟨n, hnfix, hn⟩ := p.exists_fixed_reflectionNormalizer hE f hi a ha
  have h := hb.weylAction p.inclusion f n hnfix
  rwa [hn, ← RootPairing.root_reflectionPerm] at h

/-- Mathlib base induction propagates fixedness from the simple root functors to all roots. -/
theorem all_roots_fixed_of_simple
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion) (f : G ⟶ G)
    (hi : p.inclusion ≫ f = p.inclusion)
    (hsimple : ∀ a : p.base.support,
      RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a)) (a : p.rootIndex) :
    RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a) := by
  let : p.rootDatum.IsReduced := p.isReduced
  apply p.base.induction_reflect a
    (p := fun b => RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root b))
  · intro b hb
    exact p.root_fixed_reflection hE f hi b b hb hb
  · intro b hb
    exact hsimple ⟨b, hb⟩
  · intro b c hb hc
    exact p.root_fixed_reflection hE f hi c b (hsimple ⟨c, hc⟩) hb

/-- Closed torus-and-root generation concludes identity from fixed simple root
functors, retaining the actual pair-existence and self-centralization premises. -/
theorem eq_id_of_fixed_simple_rootSubgroups
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion)
    (hself : torusCentralizer p.inclusion = SubgroupFunctor.range p.inclusion)
    (f : G ⟶ G) (hi : p.inclusion ≫ f = p.inclusion)
    (hsimple : ∀ a : p.base.support,
      RelativeRoot.IsFixedBy p.inclusion f (p.rootDatum.root a)) : f = 𝟙 G := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := p.isConnectedReductive.connectedSpace
  obtain ⟨D, d, hdrep, hdclosed⟩ := endomorphismFixedSubgroup_isClosedRepresentable f
  apply (endomorphismFixedSubgroup_eq_top_iff f).mp
  rw [← hdrep.2]
  apply range_eq_top_of_selfCentralizing_torus_and_rootSubgroups p.inclusion
    p.isSplitTorus hself d hdclosed
  · rw [hdrep.2]
    exact (range_le_endomorphismFixedSubgroup_iff f p.inclusion).mpr hi
  · intro α hα
    obtain ⟨a, rfl⟩ : ∃ a : p.rootIndex, p.rootDatum.root a = α := by
      rw [← Set.mem_range, p.isRootDatum.2.1]
      exact hα
    rw [hdrep.2]
    exact p.all_roots_fixed_of_simple hE f hi hsimple a

end SplitPinning

end Langlands.GroupScheme
