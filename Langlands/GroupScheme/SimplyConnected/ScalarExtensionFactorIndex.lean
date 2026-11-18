import Langlands.GroupScheme.Reductive.StarActionScalarExtension
import Langlands.GroupScheme.SimplyConnected.GeometricFactorTorus
import Langlands.GroupScheme.SimplyConnected.RootFactorPlacement
import Langlands.GroupScheme.Rational.CrossTorusRootTransport

/-! # Actual root-factor indices in the scalar-extension pinning comparison -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GaloisPinningData.ScalarExtension

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : GaloisPinningData k L G} (F : ScalarExtension (E := E) p)

local instance scalarFactorIndex_originalAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance scalarFactorIndex_iteratedAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap E L)).obj
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    (CategoryTheory.Limits.pullback.snd G.X.hom _) _)
  infer_instance

/-- The actual scalar-extension root comparison retains the entire all-test
root subgroup through the canonical ambient tower isomorphism. -/
theorem root_subgroup_comap (r : p.rootIndex) :
    (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj p.torus)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map p.inclusion) (p.rootDatum.root r)).comap F.groupIso.hom =
      RelativeRoot.subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap E L)).obj F.pinning.torus)
        ((GroupScheme.baseChange (algebraBaseMap E L)).map F.pinning.inclusion)
        (F.pinning.rootDatum.root (F.rootEquiv.indexEquiv r)) := by
  have hr : F.pinning.rootDatum.root (F.rootEquiv.indexEquiv r) =
      F.torusIso.hom ≫ p.rootDatum.root r :=
    (RootPairing.Hom.root_weightMap_apply _ _ r F.rootEquiv.toHom).symm.trans (F.weight_eq _)
  have hc : characterLattice.congr F.torusIso
      (F.pinning.rootDatum.root (F.rootEquiv.indexEquiv r)) = p.rootDatum.root r := by
    rw [characterLattice.congr_apply, hr, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h := RelativeRoot.subgroup_comap_of_transport F.torusIso F.groupIso F.inclusion_comp
    (F.pinning.rootDatum.root (F.rootEquiv.indexEquiv r))
  rw [hc] at h
  exact h

/-- Every actual geometric normal-factor label is retained by the full
scalar-extension root equivalence, not only its abstract Cartan matrix. -/
theorem rootDatumFactorIndex_eq
    (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (r : p.rootIndex) :
    (D.ofIso F.groupIso).rootDatumFactorIndex
      (T := (CommGroupScheme.baseChange (algebraBaseMap E L)).obj F.pinning.torus)
      (hG.of_iso F.groupIso) F.pinning.isSplitTorus
      ((GroupScheme.baseChange (algebraBaseMap E L)).map F.pinning.inclusion)
      F.pinning.isMaximalTorus F.pinning.isRootDatum
        (F.rootEquiv.indexEquiv r) =
      D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum r := by
  let D' := D.ofIso F.groupIso
  let i := D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum r
  have hroot : F.pinning.rootDatum.root (F.rootEquiv.indexEquiv r) ∈
      relativeRoots (T := (CommGroupScheme.baseChange (algebraBaseMap E L)).obj F.pinning.torus)
        ((GroupScheme.baseChange (algebraBaseMap E L)).map F.pinning.inclusion) := by
    rw [relativeRoots_eq_roots, ← F.pinning.isRootDatum.2.1]
    exact Set.mem_range_self _
  apply D'.root_subgroup_factor_unique
    (T := (CommGroupScheme.baseChange (algebraBaseMap E L)).obj F.pinning.torus)
    (hG.of_iso F.groupIso) F.pinning.isSplitTorus
    ((GroupScheme.baseChange (algebraBaseMap E L)).map F.pinning.inclusion)
    F.pinning.isMaximalTorus hroot
  · exact D'.root_subgroup_le_rootFactorIndex (hG.of_iso F.groupIso) F.pinning.isSplitTorus _
      F.pinning.isMaximalTorus _
  · have hi : SubgroupFunctor.range (D'.inclusion i) =
        (SubgroupFunctor.range (D.inclusion i)).comap F.groupIso.hom := by
      rw [SimplyConnectedAlmostSimpleProduct.ofIso_inclusion]
      exact SubgroupFunctor.range_comp_iso (D.inclusion i) F.groupIso.symm
    rw [hi, ← F.root_subgroup_comap r]
    intro U x hx
    exact D.root_subgroup_le_rootFactorIndex hG p.isSplitTorus _ p.isMaximalTorus _ U hx

/-- The full scalar-extension root equivalence preserves every actual factor
label of a supplied geometric product presentation. -/
def PreservesFactorIndices
    (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) : Prop :=
  ∀ r : p.rootIndex,
    (D.ofIso F.groupIso).rootDatumFactorIndex
      (T := (CommGroupScheme.baseChange (algebraBaseMap E L)).obj F.pinning.torus)
      (hG.of_iso F.groupIso) F.pinning.isSplitTorus
      ((GroupScheme.baseChange (algebraBaseMap E L)).map F.pinning.inclusion)
      F.pinning.isMaximalTorus F.pinning.isRootDatum (F.rootEquiv.indexEquiv r) =
    D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum r

/-- All geometric factor indices are preserved. -/
theorem preservesFactorIndices
    (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) :
    F.PreservesFactorIndices D hG := F.rootDatumFactorIndex_eq D hG

end Langlands.GroupScheme.GaloisPinningData.ScalarExtension
