import Langlands.GroupScheme.SimplyConnected.RootFactorPlacement
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorStabilizer
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport
import Langlands.GroupScheme.Reductive.TitsCartanComponentTransport

/-! # Full Galois and star covariance of actual root-factor placement -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
  {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hP : IsRootDatumOf t P)

/-- A nonzero ordered pairing forces equality of actual root factors. -/
theorem rootDatumFactorIndex_eq_of_pairing_ne_zero (r s : J) (h : P.pairing r s ≠ 0) :
    D.rootDatumFactorIndex hG hT t ht hP r = D.rootDatumFactorIndex hG hT t ht hP s := by
  by_contra hne
  exact h (D.pairing_eq_zero_of_rootDatumFactorIndex_ne hG hT t ht hP r s hne)

/-- Abstract root reflections preserve actual normal-factor placement. -/
theorem rootDatumFactorIndex_reflection (r s : J) :
    D.rootDatumFactorIndex hG hT t ht hP (P.reflectionPerm s r) =
      D.rootDatumFactorIndex hG hT t ht hP r := by
  by_cases hzero : P.pairing r s = 0
  · rw [P.reflectionPerm_eq_of_pairing_eq_zero hzero]
  · have hpair : P.pairing (P.reflectionPerm s r) s ≠ 0 := by
      rw [← P.pairing_reflectionPerm s r s, P.pairing_reflectionPerm_self_right]
      exact neg_ne_zero.mpr hzero
    exact (D.rootDatumFactorIndex_eq_of_pairing_ne_zero hG hT t ht hP _ _ hpair).trans
      (D.rootDatumFactorIndex_eq_of_pairing_ne_zero hG hT t ht hP _ _ hzero).symm

/-- Every abstract Weyl correction fixes the actual normal-factor index. -/
theorem rootDatumFactorIndex_weyl {w : P.Aut} (hw : w ∈ P.weylGroup) (r : J) :
    D.rootDatumFactorIndex hG hT t ht hP (w.indexEquiv r) =
      D.rootDatumFactorIndex hG hT t ht hP r := by
  induction hw using RootPairing.weylGroup.induction generalizing r with
  | mem s => exact D.rootDatumFactorIndex_reflection hG hT t ht hP r s
  | one => rfl
  | mul x y hx hy ihx ihy =>
    exact (ihx (y.indexEquiv r)).trans (ihy r)

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

namespace Langlands.GroupScheme.SubgroupFunctor

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Canonical coefficient transport preserves every all-test subgroup inclusion. -/
theorem galoisTransport_mono (σ : L ≃ₐ[k] L)
    {F H : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)}
    (h : F ≤ H) : galoisTransport k L G σ F ≤ galoisTransport k L G σ H := by
  intro U x hx
  change x ∈ (descentTransport (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G H).carrier U
  change x ∈ (descentTransport (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G F).carrier U at hx
  rw [mem_descentTransport_iff_descentPoint] at hx ⊢
  exact h _ hx

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
  (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
  (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
  (p : GaloisPinningData k L G)

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- Ordinary Galois transport takes the actual factor of a root to the
canonical Galois transport of that product factor. -/
theorem rootDatumFactorIndex_galois (σ : L ≃ₐ[k] L) (r : p.rootIndex) :
    D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum
        ((p.galoisAction σ).indexEquiv r) =
      D.galoisFactorIndex σ
        (D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum r) := by
  let t := (GroupScheme.baseChange (algebraBaseMap k L)).map p.inclusion
  have hroot (s : p.rootIndex) : p.rootDatum.root s ∈ relativeRoots t := by
    rw [relativeRoots_eq_roots, ← p.isRootDatum.2.1]
    exact Set.mem_range_self s
  apply D.root_subgroup_factor_unique hG p.isSplitTorus t p.isMaximalTorus
    (hroot ((p.galoisAction σ).indexEquiv r))
  · exact D.root_subgroup_le_rootFactorIndex hG p.isSplitTorus t p.isMaximalTorus _
  · have hle := SubgroupFunctor.galoisTransport_mono k L G σ
      (D.root_subgroup_le_rootFactorIndex hG p.isSplitTorus t p.isMaximalTorus (hroot r))
    rw [← D.range_inclusion_galoisFactorIndex] at hle
    rw [RelativeRoot.subgroup_galoisTransport] at hle
    have he : p.rootDatum.root ((p.galoisAction σ).indexEquiv r) =
        characterLattice.galoisRepresentation k L p.torus σ (p.rootDatum.root r) := by
      exact (RootPairing.Hom.root_weightMap_apply _ _ r (p.galoisAction σ).toHom).symm
    rw [he]
    exact hle

/-- The full star action has exactly the canonical permutation of actual
normal product factors; its Weyl correction contributes no factor permutation. -/
theorem rootDatumFactorIndex_star (σ : L ≃ₐ[k] L) (r : p.rootIndex) :
    D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum
        ((p.starAction σ).val.indexEquiv r) =
      D.galoisFactorIndex σ
        (D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum r) := by
  obtain ⟨w, hw⟩ := p.exists_weyl_mul_galoisAction_eq_starAction σ
  rw [← hw]
  exact (D.rootDatumFactorIndex_weyl hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum
    w.property ((p.galoisAction σ).indexEquiv r)).trans
    (D.rootDatumFactorIndex_galois hG p σ r)

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom]
  (d : TitsIndexData G)
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))
  (hG : IsSemisimple
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- The actual geometric normal factor containing a specified simple root subgroup. -/
def geometricFactorIndex (a : d.Vertex) : D.Index :=
  D.rootDatumFactorIndex hG d.pinning.isSplitTorus _ d.pinning.isMaximalTorus
    d.pinning.isRootDatum a.val

omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom] in
/-- All vertices of one entire Cartan component have the same actual factor. -/
theorem geometricFactorIndex_eq_of_cartanConnected {a b : d.Vertex}
    (h : d.CartanConnected a b) :
    d.geometricFactorIndex D hG a = d.geometricFactorIndex D hG b :=
  D.rootDatumFactorIndex_eq_of_cartanConnected hG d.pinning.isSplitTorus _
    d.pinning.isMaximalTorus d.pinning.isRootDatum d.pinning.base h

/-- Full absolute-Galois star covariance of the actual simple-root factor. -/
theorem geometricFactorIndex_star (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (a : d.Vertex) :
    d.geometricFactorIndex D hG (d.star σ a) =
      D.galoisFactorIndex σ (d.geometricFactorIndex D hG a) :=
  D.rootDatumFactorIndex_star hG d.pinning σ a.val

/-- Every component-stabilizing Galois element fixes its actual geometric factor. -/
theorem cartanComponentStabilizer_le_factorStabilizer (a : d.Vertex) :
    d.cartanComponentStabilizer a ≤
      D.galoisFactorStabilizer (d.geometricFactorIndex D hG a) := by
  intro σ hσ
  change D.galoisFactorIndex σ (d.geometricFactorIndex D hG a) = _
  rw [← d.geometricFactorIndex_star D hG]
  exact (d.geometricFactorIndex_eq_of_cartanConnected D hG hσ).symm

/-- Once the reverse component identification is supplied, the full subgroups
agree exactly, rather than only their finite permutation images. -/
theorem cartanComponentStabilizer_eq_factorStabilizer
    (hconn : ∀ a b : d.Vertex,
      d.geometricFactorIndex D hG a = d.geometricFactorIndex D hG b → d.CartanConnected a b)
    (a : d.Vertex) :
    d.cartanComponentStabilizer a =
      D.galoisFactorStabilizer (d.geometricFactorIndex D hG a) := by
  apply le_antisymm (d.cartanComponentStabilizer_le_factorStabilizer D hG a)
  intro σ hσ
  apply hconn a (d.star σ a)
  rw [d.geometricFactorIndex_star D hG]
  exact hσ.symm

end Langlands.GroupScheme.TitsIndexData
