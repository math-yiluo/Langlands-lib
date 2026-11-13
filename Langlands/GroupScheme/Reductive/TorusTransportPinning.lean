import Langlands.GroupScheme.Reductive.RootDatumTorusTransport
import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Reductive.TitsIndex

/-! # Pinnings transported through an aligned torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section RootDatum

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))} {J : Type v}
  (e : T ≅ T') (P : RootDatum J (characterLattice T) (cocharacterLattice T))

/-- The actual lattice transport is an equivalence of root data with unchanged indices. -/
def torusTransportRootDatumEquiv : P.Equiv (torusTransportRootDatum e P) where
  weightMap := (characterLattice.congr e).toIntLinearEquiv
  coweightMap := (cocharacterLattice.congr e).symm.toIntLinearEquiv
  indexEquiv := Equiv.refl J
  weight_coweight_transpose := by
    ext y x
    obtain ⟨z, rfl⟩ := (cocharacterLattice.congr e).surjective y
    change (torusTransportRootDatum e P).toLinearMap (characterLattice.congr e x)
      (cocharacterLattice.congr e z) =
      P.toLinearMap x ((cocharacterLattice.congr e).symm (cocharacterLattice.congr e z))
    rw [AddEquiv.symm_apply_apply, torusTransportRootDatum_pairing]
  root_weightMap := rfl
  coroot_coweightMap := by
    funext a
    exact (cocharacterLattice.congr e).symm_apply_apply (P.coroot a)
  bijective_weightMap := (characterLattice.congr e).bijective
  bijective_coweightMap := (cocharacterLattice.congr e).symm.bijective

/-- The supplied base transported through the torus isomorphism. -/
def torusTransportBase (b : P.Base) : (torusTransportRootDatum e P).Base :=
  b.map (torusTransportRootDatumEquiv e P)

@[simp] theorem torusTransportBase_support (b : P.Base) :
    (torusTransportBase e P b).support = b.support := by
  classical
  simp only [torusTransportBase, RootPairing.Base.support_map_eq,
    torusTransportRootDatumEquiv, Equiv.coe_refl, Finset.image_id]

/-- The simple vertices retain their original root indices. -/
def torusTransportSimpleEquiv (b : P.Base) :
    b.support ≃ (torusTransportBase e P b).support :=
  Equiv.subtypeEquivRight fun a => by rw [torusTransportBase_support]

@[simp] theorem torusTransportRootDatum_pairing_indices (a b : J) :
    (torusTransportRootDatum e P).pairing a b = P.pairing a b :=
  (torusTransportRootDatumEquiv e P).toHom.pairing

/-- Reducedness is preserved by the actual lattice isomorphism. -/
theorem torusTransportRootDatum_isReduced [P.IsReduced] :
    (torusTransportRootDatum e P).IsReduced := by
  refine ⟨fun a c h => ?_⟩
  have h' : ¬ LinearIndependent ℤ ![P.root a, P.root c] := by
    intro hli
    apply h
    let f : characterLattice T ≃ₗ[ℤ] characterLattice T' :=
      (characterLattice.congr e).toIntLinearEquiv
    convert hli.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr f.injective) using 1
    ext j
    fin_cases j <;> rfl
  rcases RootPairing.IsReduced.eq_or_eq_neg a c h' with h | h
  · exact Or.inl (congrArg (characterLattice.congr e) h)
  · exact Or.inr (by
      simpa only [torusTransportRootDatum_root, map_neg] using
        congrArg (characterLattice.congr e) h)

end RootDatum

namespace GaloisPinningData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of (SeparableClosure k)))}
  [IsAffineHom H.X.hom]

local notation "bK" => algebraBaseMap k (SeparableClosure k)
local notation "F" => GroupScheme.baseChange bK
local notation "C" => CommGroupScheme.baseChange bK

/-- Transport a prescribed split pinning to a maximal torus defined over the ground field. -/
def ofTorusIso (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (q : SplitPinning H)
    (e : (C).obj T ≅ q.torus) (Φ : (F).obj G ≅ H)
    (he : (F).map i ≫ Φ.hom = CommGroupScheme.groupHom e.hom ≫ q.inclusion) :
    GaloisPinningData k (SeparableClosure k) G := by
  have := hG.smooth
  let hGE := connectedReductiveFieldExtensionStatement k (SeparableClosure k) G hG
  let hsplit := isSplitTorus_separableClosure T hi.1
  let hiE : IsMaximalTorus (T := (C).obj T) ((F).map i) :=
    (maximalTorusBaseChange k (SeparableClosure k) G T i hi.1 hi.2.1).mp hi
  let P := torusTransportRootDatum e.symm q.rootDatum
  have hsq : q.inclusion ≫ Φ.inv = CommGroupScheme.groupHom e.inv ≫ (F).map i := by
    rw [Iso.comp_inv_eq, Category.assoc, he, ← Category.assoc]
    change q.inclusion = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ q.inclusion
    rw [Iso.inv_hom_id]
    exact (Category.id_comp q.inclusion).symm
  have hP : IsRootDatumOf (T := (C).obj T) ((F).map i) P :=
    q.isRootDatum.torusTransport e.symm Φ.symm hsq
  have := q.isReduced
  exact {
    torus := T
    inclusion := i
    isConnectedReductive := hGE
    isSplitTorus := hsplit
    isMaximalTorus := hiE
    rootIndex := q.rootIndex
    rootDatum := P
    isRootDatum := hP
    isReduced := torusTransportRootDatum_isReduced e.symm q.rootDatum
    base := torusTransportBase e.symm q.rootDatum q.base
    pinning := RootPinning.ofSplitMaximalTorus hGE hsplit _ hiE P hP
      (torusTransportBase e.symm q.rootDatum q.base) }

variable (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (q : SplitPinning H)
  (e : (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T ≅ q.torus)
  (Φ : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅ H)
  (he : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map i ≫ Φ.hom =
    CommGroupScheme.groupHom e.hom ≫ q.inclusion)

/-- The transported pinning retains the supplied simple-root indices. -/
def ofTorusIsoSimpleEquiv :
    q.base.support ≃ (ofTorusIso hG T i hi q e Φ he).base.support :=
  torusTransportSimpleEquiv e.symm q.rootDatum q.base

@[simp] theorem ofTorusIsoSimpleEquiv_val (a : q.base.support) :
    (ofTorusIsoSimpleEquiv hG T i hi q e Φ he a).val = a.val := rfl

/-- The transported pinning retains every Cartan pairing with its original indices. -/
theorem ofTorusIso_pairing (a b : q.rootIndex) :
    (ofTorusIso hG T i hi q e Φ he).rootDatum.pairing a b = q.rootDatum.pairing a b :=
  torusTransportRootDatum_pairing_indices e.symm q.rootDatum a b

/-- A prescribed map to the split torus computes the actual descended restriction. -/
theorem ofTorusIso_absoluteRootRestriction
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (f : S ⟶ T) (ψ : (C).obj S ⟶ q.torus) (hψ : (C).map f ≫ e.hom = ψ)
    (a : q.rootIndex) :
    absoluteRootRestriction (ofTorusIso hG T i hi q e Φ he) S hS f a =
      (characterLattice.baseChangeEquiv bK S hS).symm (ψ ≫ q.rootDatum.root a) := by
  change (characterLattice.baseChangeEquiv bK S hS).symm
    ((C).map f ≫ characterLattice.congr e.symm (q.rootDatum.root a)) = _
  congr 1
  change (C).map f ≫ (e.hom ≫ q.rootDatum.root a) = ψ ≫ q.rootDatum.root a
  rw [← Category.assoc, hψ]

end GaloisPinningData

end Langlands.GroupScheme
