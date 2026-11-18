import Langlands.GroupScheme.SimplyConnected.FactorRootBase
import Langlands.GroupScheme.SimplyConnected.RootFactorGalois
import Langlands.GroupScheme.Reductive.SplitAlmostSimpleCartanConnected
import Langlands.GroupScheme.Reductive.RootDatumExistence

/-! # Actual almost-simple product factors are exactly the Cartan components -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G) (p : SplitPinning G)

/-- Simple vertices belong to the same actual product factor exactly when they
belong to the same full integral Cartan component. -/
theorem rootDatumFactorIndex_eq_iff_cartanConnected (a c : p.base.support) :
    D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum a.val =
      D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum c.val ↔
    Relation.EqvGen
      (fun x y : p.base.support => x ≠ y ∧ p.rootDatum.pairing x.val y.val ≠ 0) a c := by
  constructor
  · intro hac
    let i := D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion p.isMaximalTorus
      p.isRootDatum a.val
    let F := D.factorMaximalTorus hG.isConnectedReductive p.inclusion p.isSplitTorus
      p.isMaximalTorus i
    let hA := (D.isSimplyConnected i).isSemisimple.isConnectedReductive
    let : IsAffineHom (D.factor i).X.hom := hA.isAffineHom
    obtain ⟨K, hK, Q, hQ, hred⟩ :=
      rootDatumExistence k (D.factor i) hA F.torus F.split F.subgroupHom F.isMaximalTorus
    let : Finite K := hK
    let : Q.IsReduced := hred
    let B := F.inducedBase D hG p hQ
    let e := F.simpleRootIndexEquiv D hG p hQ
    let f : B.support → p.base.support := fun b => (e b).val
    have hf : Function.Injective f := Subtype.val_injective.comp e.injective
    have hpair (b d : B.support) :
        p.rootDatum.pairing (f b).val (f d).val = Q.pairing b.val d.val :=
      F.pairing_simpleRootIndexEquiv D hG p hQ b d
    have hmap {b d : B.support}
        (h : Relation.EqvGen (fun x y : B.support => x ≠ y ∧ Q.pairing x.val y.val ≠ 0) b d) :
        Relation.EqvGen
          (fun x y : p.base.support => x ≠ y ∧ p.rootDatum.pairing x.val y.val ≠ 0)
          (f b) (f d) := by
      induction h with
      | rel b d hbd =>
        exact Relation.EqvGen.rel _ _ ⟨fun he => hbd.1 (hf he), by
          rw [hpair]
          exact hbd.2⟩
      | refl b => exact Relation.EqvGen.refl _
      | symm b d _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans b d z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    let a' : B.support := e.symm ⟨a, rfl⟩
    let c' : B.support := e.symm ⟨c, hac.symm⟩
    have hconn := cartanConnected_of_splitAlmostSimple (D.isAlmostSimple i) F.split
      F.isMaximalTorus hQ B a' c'
    have hm := hmap hconn
    simpa only [f, a', c', Equiv.apply_symm_apply] using hm
  · exact D.rootDatumFactorIndex_eq_of_cartanConnected hG p.isSplitTorus p.inclusion
      p.isMaximalTorus p.isRootDatum p.base

namespace FactorMaximalTorus

variable {i : D.Index} (F : D.FactorMaximalTorus p.inclusion i)
  {K : Type u} [Finite K]
  {Q : RootDatum K (characterLattice F.torus) (cocharacterLattice F.torus)}
  (hQ : IsRootDatumOf F.subgroupHom Q) [Q.IsReduced]
  (a : p.base.support)
  (ha : D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion p.isMaximalTorus
    p.isRootDatum a.val = i)

/-- The factor's actual simple base realizes the entire selected ambient
Cartan component. -/
def simpleCartanComponentEquiv :
    (F.inducedBase D hG p hQ).support ≃
      {b : p.base.support // Relation.EqvGen
        (fun x y : p.base.support => x ≠ y ∧ p.rootDatum.pairing x.val y.val ≠ 0) a b} :=
  (F.simpleRootIndexEquiv D hG p hQ).trans
    (Equiv.subtypeEquivRight (fun b => by
      constructor
      · intro hb
        exact (D.rootDatumFactorIndex_eq_iff_cartanConnected hG p a b).mp
          (ha.trans hb.symm)
      · intro hb
        exact ((D.rootDatumFactorIndex_eq_iff_cartanConnected hG p a b).mpr hb).symm.trans ha))

/-- Every ordered entry agrees on the entire selected component. -/
theorem pairing_simpleCartanComponentEquiv
    (b c : (F.inducedBase D hG p hQ).support) :
    p.rootDatum.pairing (F.simpleCartanComponentEquiv D hG p hQ a ha b).val.val
        (F.simpleCartanComponentEquiv D hG p hQ a ha c).val.val = Q.pairing b.val c.val :=
  F.pairing_simpleRootIndexEquiv D hG p hQ b c

end FactorMaximalTorus

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))
  (hG : IsSemisimple
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))

local instance factorCartanComponent_baseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- Equality of actual geometric normal factors is precisely full Cartan
connectivity for the prescribed actual Tits index. -/
theorem geometricFactorIndex_eq_iff_cartanConnected (a b : d.Vertex) :
    d.geometricFactorIndex D hG a = d.geometricFactorIndex D hG b ↔ d.CartanConnected a b :=
  D.rootDatumFactorIndex_eq_iff_cartanConnected hG d.pinning.toSplitPinning a b

/-- The exact equivalence of the actual factor fibre with the entire chosen
Cartan component, retaining the original simple vertices. -/
def geometricFactorFibreComponentEquiv (a : d.Vertex) :
    {b : d.Vertex // d.geometricFactorIndex D hG b = d.geometricFactorIndex D hG a} ≃
      d.CartanComponent a :=
  Equiv.subtypeEquivRight (fun b => by
    rw [eq_comm]
    exact d.geometricFactorIndex_eq_iff_cartanConnected D hG a b)

/-- The full absolute-Galois component stabilizer equals the actual geometric
normal-factor stabilizer, with no remaining connectivity premise. -/
theorem cartanComponentStabilizer_eq_geometricFactorStabilizer (a : d.Vertex) :
    letI : Smooth
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom :=
        hG.isConnectedReductive.smooth
    d.cartanComponentStabilizer a =
      D.galoisFactorStabilizer (d.geometricFactorIndex D hG a) := by
  let : Smooth
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom :=
    hG.isConnectedReductive.smooth
  exact d.cartanComponentStabilizer_eq_factorStabilizer D hG
    (fun a b h => (d.geometricFactorIndex_eq_iff_cartanConnected D hG a b).mp h) a

end Langlands.GroupScheme.TitsIndexData
