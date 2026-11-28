import Langlands.GroupScheme.SimplyConnected.FactorCartanComponent
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction

/-! # Simple roots meet every geometric normal factor -/

noncomputable section

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

/-- Every noncommutative factor of the simply connected product has a
simple root in the specified split pinning. -/
theorem rootDatumFactorIndex_surjective_on_base {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G) (p : SplitPinning G) :
    Function.Surjective (fun a : p.base.support =>
      D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum a.val) := by
  classical
  intro i
  let M := D.factorMaximalTorus hG.isConnectedReductive p.inclusion p.isSplitTorus p.isMaximalTorus i
  have hA := D.isAlmostSimple i
  let : IsAffineHom (D.factor i).X.hom := hA.isSemisimple.isConnectedReductive.isAffineHom
  obtain ⟨K, hK, Q, hQ, hred⟩ := rootDatumExistence k (D.factor i)
    hA.isSemisimple.isConnectedReductive M.torus M.split M.subgroupHom M.isMaximalTorus
  let : Finite K := hK
  let : Q.IsReduced := hred
  let e := M.simpleRootIndexEquiv D hG p hQ
  let B := M.inducedBase D hG p hQ
  obtain ⟨α, hα⟩ := hA.relativeRoots_nonempty_of_split_maximalTorus M.subgroupHom M.split M.isMaximalTorus
  have hq : α ∈ Set.range Q.root := by rw [hQ.2.1, ← relativeRoots_eq_roots]; exact hα
  obtain ⟨a, rfl⟩ := hq
  have hB : B.support.Nonempty := by
    by_contra hb
    have he : B.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
    have h := B.root_mem_or_neg_mem a
    apply Q.ne_zero a
    simpa only [he, Finset.coe_empty, Set.image_empty, AddSubmonoid.closure_empty,
      AddSubmonoid.mem_bot, neg_eq_zero, or_self] using h
  obtain ⟨z, hz⟩ := hB
  let v := e ⟨z, hz⟩
  exact ⟨v.val, v.property⟩

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
