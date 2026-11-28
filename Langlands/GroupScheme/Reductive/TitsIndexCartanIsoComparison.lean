import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Descent.Data

/-! # Cartan matrices of Tits indices of groups isomorphic over the separable closure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Split pinnings of isomorphic groups have root data related by an equivalence
carrying the first chosen base onto the second. -/
theorem exists_rootDatumEquiv_base_of_iso (p : SplitPinning G) (q : SplitPinning H)
    (f : G ≅ H) :
    ∃ e : RootPairing.Equiv p.rootDatum q.rootDatum,
      ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support := by
  have hH := q.isConnectedReductive
  have := hH.smooth
  have := hH.connectedSpace
  have hi : IsMaximalSplitTorus (p.inclusion ≫ f.hom) :=
    (p.isMaximalTorus.comp_iso f).isMaximalSplitTorus p.isSplitTorus
  have hj : IsMaximalSplitTorus q.inclusion :=
    q.isMaximalTorus.isMaximalSplitTorus q.isSplitTorus
  obtain ⟨g, t, ht⟩ := smoothMaximalSplitTorusConjugacy k H p.torus q.torus _ _ hi hj
  let φ : q.torus ≅ p.torus := (CommGroupScheme.isoOfGroupIso t).symm
  let F : H ≅ G := (f ≪≫ H.innerIso g).symm
  have hsq : q.inclusion ≫ F.hom = CommGroupScheme.groupHom φ.hom ≫ p.inclusion := by
    change q.inclusion ≫ (H.innerIso g).inv ≫ f.inv = t.inv ≫ p.inclusion
    have hq : q.inclusion = t.inv ≫ (p.inclusion ≫ f.hom) ≫ (H.innerIso g).hom := by
      rw [ht, Iso.inv_hom_id_assoc]
    rw [hq]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  let e₀ : RootPairing.Equiv p.rootDatum q.rootDatum :=
    rootDatumEquivOfTorusCompatibleIso q.isConnectedReductive p.isConnectedReductive
      q.isSplitTorus p.isSplitTorus q.isMaximalTorus p.isMaximalTorus F φ hsq
      q.isRootDatum p.isRootDatum
  obtain ⟨w, -, hw⟩ := StarActionIndependence.exists_weyl_comp_preserves_base p q e₀
  exact ⟨RootPairing.Equiv.comp w e₀, hw⟩

end SplitPinning

/-- An isomorphism of two groups after a separable algebraic field extension gives
an isomorphism after extension to the separable closure, through any embedding of
the extension field into the separable closure. -/
def separableClosureIsoOfBaseChangeIso {k L : Type u} [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (f : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj H) :
    (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H := by
  let ι : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := ι.toRingHom.toAlgebra
  have h : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
      algebraBaseMap k (SeparableClosure k) := by
    dsimp only [algebraBaseMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
      (RingHom.ext fun x => ι.commutes x)
  exact (Descent.pullbackComparison _ _ _ h G).symm ≪≫
    (GroupScheme.baseChange (algebraBaseMap L (SeparableClosure k))).mapIso f ≪≫
      Descent.pullbackComparison _ _ _ h H

namespace TitsIndexData

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

local instance separableClosureAffine (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- Tits indices of two groups that become isomorphic over the separable closure have
simple vertices in bijection, with equal Cartan entries. -/
theorem exists_cartanEquiv_of_separableClosureIso (d : TitsIndexData G) (d' : TitsIndexData H)
    (f : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H) :
    ∃ v : d.Vertex ≃ d'.Vertex, ∀ a b, d'.cartan (v a) (v b) = d.cartan a b := by
  obtain ⟨E, hE⟩ := SplitPinning.exists_rootDatumEquiv_base_of_iso
    d.pinning.toSplitPinning d'.pinning.toSplitPinning f
  exact ⟨E.indexEquiv.subtypeEquiv hE, fun a b => E.toHom.pairing⟩

end TitsIndexData

end Langlands.GroupScheme
