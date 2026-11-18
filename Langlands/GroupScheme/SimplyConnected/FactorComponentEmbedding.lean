import Langlands.GroupScheme.SimplyConnected.FactorRootBase
import Langlands.GroupScheme.Reductive.ComponentStarHom
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor

/-! # Actual product-factor pinnings embed as full orthogonal root components -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct.FactorMaximalTorus

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G) (p : SplitPinning G)
  {i : D.Index} (F : D.FactorMaximalTorus p.inclusion i)

private instance factorComponentEmbedding_factorAffine : IsAffineHom (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom

variable {K : Type u}
  {Q : RootDatum K (characterLattice F.torus) (cocharacterLattice F.torus)}
  (hQ : IsRootDatumOf F.subgroupHom Q)

local notation "idx" => F.rootIndex D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ

/-- The actual root-inflation map is a full orthogonal root-component embedding. -/
def rootComponentEmbedding : RootComponentEmbedding Q p.rootDatum where
  index := ⟨idx, F.rootIndex_injective D hG p.isSplitTorus p.inclusion p.isMaximalTorus
    p.isRootDatum hQ⟩
  weightMap := characterLattice.pullback F.projectionHom
  root_eq b := (F.rootIndex_root D hG p.isSplitTorus p.inclusion p.isMaximalTorus
    p.isRootDatum hQ b).symm
  pairing_eq := F.pairing_rootIndex D hG p.isSplitTorus p.inclusion p.isMaximalTorus
    p.isRootDatum hQ
  orthogonal b r hr :=
    D.pairing_eq_zero_of_rootDatumFactorIndex_ne hG p.isSplitTorus p.inclusion
      p.isMaximalTorus p.isRootDatum (idx b) r (by
        intro he
        apply hr
        exact F.rootIndex_surjective D hG p.isSplitTorus p.inclusion p.isMaximalTorus
          p.isRootDatum hQ (he.symm.trans (F.rootIndex_factor D hG p.isSplitTorus p.inclusion
            p.isMaximalTorus p.isRootDatum hQ b)))

variable [Finite K] [Q.IsReduced]

/-- A genuine pinning on the actual product factor, retaining the compatible
torus, supplied root datum and exact induced ambient simple base. -/
def inducedPinning : SplitPinning (D.factor i) where
  isConnectedReductive := (D.isSimplyConnected i).isSemisimple.isConnectedReductive
  torus := F.torus
  inclusion := F.subgroupHom
  isSplitTorus := F.split
  isMaximalTorus := F.isMaximalTorus
  rootIndex := K
  rootDatum := Q
  isRootDatum := hQ
  isReduced := inferInstance
  base := F.inducedBase D hG p hQ
  pinning := RootPinning.ofSplitMaximalTorus
    (D.isSimplyConnected i).isSemisimple.isConnectedReductive F.split F.subgroupHom
    F.isMaximalTorus Q hQ (F.inducedBase D hG p hQ)

/-- The actual induced pinning embeds into the ambient pinning as one full
orthogonal root component, with exact simple supports. -/
def basedComponentEmbedding :
    SplitPinning.BasedComponentEmbedding (F.inducedPinning D hG p hQ) p where
  rootEmbedding := F.rootComponentEmbedding D hG p hQ
  base_iff := F.mem_inducedBase_iff D hG p hQ

/-- Weyl correction respects the actual factor root index whenever the
original root automorphisms intertwine it. -/
theorem basedProjection_index (x : Q.Aut) (y : p.rootDatum.Aut)
    (h : ∀ b, idx (x.indexEquiv b) = y.indexEquiv (idx b)) (b : K) :
    idx (((F.inducedPinning D hG p hQ).basedRootDatumProjection x).val.indexEquiv b) =
      (p.basedRootDatumProjection y).val.indexEquiv (idx b) :=
  (F.basedComponentEmbedding D hG p hQ).basedProjection_index x y h b

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct.FactorMaximalTorus
