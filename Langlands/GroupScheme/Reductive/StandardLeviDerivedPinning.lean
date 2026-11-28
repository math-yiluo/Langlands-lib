import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Reductive.TitsKernelIndexData
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.Torus.AbsoluteCharacterIsomorphism
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters

/-! # A derived Levi pinning from a dominant cocharacter of a split pinning -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LinearAlgebra.RootDatumZeroFace

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000

/-- A torus closed in a split torus is split over the same field. -/
theorem IsTorus.isSplitTorus_of_closed_in_split
    {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS : IsTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (hf : IsClosedSubgroup (CommGroupScheme.groupHom f)) :
    IsSplitTorus S.toGrp := by
  let E := SeparableClosure k
  let b := algebraBaseMap k E
  let B := CommGroupScheme.baseChange b
  have hSE : IsSplitTorus (B.obj S).toGrp := isSplitTorus_baseChange_separableClosure hS
  let : Mono (CommGroupScheme.groupHom (B.map f)).hom.hom.left := (hf.baseChange b).mono
  have hfix (σ : E ≃ₐ[k] E) (α : characterLattice (B.obj S)) :
      characterLattice.galoisRepresentation k E S σ α = α := by
    obtain ⟨β, hβ⟩ := hSE.characterRestrict_surjective_of_mono
      (hT.baseChange b) (CommGroupScheme.groupHom (B.map f)) α
    change B.map f ≫ β = α at hβ
    rw [← hβ, characterLattice.galoisRepresentation_precompose,
      TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus T hT]
  obtain ⟨I, _, ⟨e⟩⟩ := hSE
  let A := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  have hA : IsSplitTorus A.toGrp := isSplitTorus_splitTorus I
  let e' : B.obj S ≅ B.obj A :=
    CommGroupScheme.isoOfGroupIso (e ≪≫ (splitTorus.baseChangeIso b I).symm)
  let a := characterLattice.isoOfEquivariantAbsoluteEquiv hS.isMultiplicativeType
    hA.isTorus.isMultiplicativeType (characterLattice.congr e').toIntLinearEquiv (fun σ α => by
      rw [hfix, TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus A hA])
  let aG : A.toGrp ≅ S.toGrp :=
    ⟨CommGroupScheme.groupHom a.hom, CommGroupScheme.groupHom a.inv,
      congrArg CommGroupScheme.groupHom a.hom_inv_id,
      congrArg CommGroupScheme.groupHom a.inv_hom_id⟩
  exact IsSplitTorus.of_iso aG.symm hA

variable {k : Type u} [Field k] {G M D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom D.X.hom]

/-- The zero face of an actual pinning as the based root datum of a derived Levi. -/
structure StandardLeviDerivedPinning (p : SplitPinning G) (ν : cocharacterLattice p.torus)
    (j : M ⟶ G) (i : D ⟶ M) where
  pinning : SplitPinning D
  torusMap : pinning.torus ⟶ p.torus
  torusMap_closed : IsClosedSubgroup (CommGroupScheme.groupHom torusMap)
  square : CommGroupScheme.groupHom torusMap ≫ p.inclusion = pinning.inclusion ≫ i ≫ j
  face : FaceDatum p.rootDatum p.base ν pinning.rootDatum
  vertices : pinning.base.support ≃ {a : p.base.support // p.rootDatum.root' a.val ν = 0}
  cartan_eq : ∀ a b : pinning.base.support,
    pinning.rootDatum.pairing a.val b.val = p.rootDatum.pairing (vertices a).val.val
      (vertices b).val.val

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType D.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
private theorem root_pos_iff_of_nonneg_simple (p : SplitPinning G)
    (ν : cocharacterLattice p.torus)
    (hν : ∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν)
    (a : p.rootIndex) (ha : p.rootDatum.root' a ν ≠ 0) :
    p.base.IsPos a ↔ 0 < p.rootDatum.root' a ν := by
  let P := p.rootDatum
  let f := P.toLinearMap.flip ν
  have h (x) (hx : x ∈ AddSubmonoid.closure (P.root '' p.base.support)) : 0 ≤ f x := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact hν ⟨a, ha⟩
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
  constructor
  · intro hp
    exact lt_of_le_of_ne (h _ ((isPos_iff_mem_closure p.base a).mp hp)) ha.symm
  · intro hpos
    by_contra hnp
    have hzero := h _ ((neg_mem_closure_iff_not_isPos p.base a).mpr hnp)
    rw [map_neg] at hzero
    exact (not_lt_of_ge (neg_nonneg.mp hzero)) hpos

/-- The actual derived subgroup of a cocharacter centralizer has a split
pinning on the simple zero face. It is simply connected if the ambient
group is simply connected. -/
theorem SplitPinning.standardLeviDerivedPinning (p : SplitPinning G)
    (ν : cocharacterLattice p.torus)
    (hν : ∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν)
    (j : M ⟶ G) (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ p.inclusion)).IsRepresentedBy j)
    (i : D ⟶ M) (hi : IsDerivedSubgroup i) :
    Nonempty (StandardLeviDerivedPinning p ν j i) ∧ (IsSimplyConnected G → IsSimplyConnected D) := by
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  have hjT : (torusCentralizer χ).IsRepresentedBy j :=
    (torusCentralizer_gm_eq_dynamicCentralizer χ).symm ▸ hj
  have hjc := isSplitTorus_gm.isClosedSubgroup_torusCentralizer χ hjT
  have hM := splitTorusCentralizerReductive k G p.isConnectedReductive (Gm _) χ
    isSplitTorus_gm M j hjT
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth M.X.hom := hM.smooth
  let : IsClosedImmersion i.hom.hom.left := hi.1
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let t := hjT.liftOfLE p.inclusion
    (range_le_torusCentralizer_of_factor χ p.inclusion (CommGroupScheme.groupHom ν) rfl)
  have ht : t ≫ j = p.inclusion := hjT.liftOfLE_comp _ _
  have htmax : IsMaximalTorus t := IsMaximalTorus.of_comp hjc (ht.symm ▸ p.isMaximalTorus)
  let TD := commutativeSubgroupIntersection t i
  let tD : TD.toGrp ⟶ D := commutativeSubgroupIntersectionSnd t i
  let φ : TD ⟶ p.torus := Additive.ofMul (commutativeSubgroupIntersectionFst t i)
  have hφ : CommGroupScheme.groupHom φ ≫ t = tD ≫ i :=
    commutativeSubgroupIntersection_condition t i
  have hφc : IsClosedSubgroup (CommGroupScheme.groupHom φ) :=
    isClosedSubgroup_commutativeSubgroupIntersectionFst t i hi.1
  have htd := isMaximalTorus_commutativeSubgroupIntersectionSnd_derived hM i hi t htmax
  have hsplitD := htd.1.isSplitTorus_of_closed_in_split p.isSplitTorus φ hφc
  have hD := hi.isConnectedReductive hM
  obtain ⟨K, hK, Q, hQ, hQred⟩ := rootDatumExistence k D hD TD hsplitD tD htd
  let : Finite K := hK
  obtain ⟨w, hw⟩ := exists_derivedCentralizerRootEquiv χ isSplitTorus_gm j hjT hM
    p.inclusion p.isSplitTorus p.isRootDatum t ht htmax ν rfl i hi tD hsplitD htd φ hφ.symm hQ
  have hzero (a : p.rootIndex) :
      ν ≫ p.rootDatum.root a = 0 ↔ p.rootDatum.root' a ν = 0 := by
    change _ ↔ p.rootDatum.toLinearMap (p.rootDatum.root a) ν = _
    rw [p.isRootDatum.1, latticePairing_apply]
    exact (gmEndEquiv k).map_eq_zero_iff.symm
  let : Mono (CommGroupScheme.groupHom φ).hom.hom.left := hφc.mono
  let F : FaceDatum p.rootDatum p.base ν Q :=
    { sign := root_pos_iff_of_nonneg_simple p ν hν
      weightMap := characterPrecompInt φ
      coweightMap := RealTorusSpace.cocharacterMapInt φ
      coweightMap_injective := RealTorusSpace.cocharacterMapInt_injective _
      pairing_comm := fun x y => by rw [hQ.1, p.isRootDatum.1]; exact latticePairing_precomp _ _ _
      indexEquiv := w.trans (Equiv.subtypeEquivRight hzero)
      root_eq := fun q => (hw q).1
      coroot_eq := fun q => (hw q).2 }
  let q : SplitPinning D :=
    { isConnectedReductive := hD
      torus := TD
      inclusion := tD
      isSplitTorus := hsplitD
      isMaximalTorus := htd
      rootIndex := K
      rootDatum := Q
      isRootDatum := hQ
      isReduced := hQred
      base := F.base
      pinning := RootPinning.ofSplitMaximalTorus hD hsplitD tD htd Q hQ F.base }
  let v : q.base.support ≃ {a : p.base.support // p.rootDatum.root' a.val ν = 0} :=
    { toFun := fun a => ⟨⟨(F.indexEquiv a.val).val, (F.mem_base_support a.val).mp a.property⟩,
        F.root'_index a.val⟩
      invFun := fun b => ⟨F.indexEquiv.symm ⟨b.val.val, b.property⟩,
        (F.mem_base_support _).mpr (by rw [Equiv.apply_symm_apply]; exact b.val.property)⟩
      left_inv := fun a => Subtype.ext (F.indexEquiv.symm_apply_apply a.val)
      right_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        change (F.indexEquiv (F.indexEquiv.symm ⟨b.val.val, b.property⟩)).val = b.val.val
        rw [Equiv.apply_symm_apply] }
  refine ⟨⟨⟨q, φ, hφc, ?_, F, v, fun a b => F.pairing_eq a.val b.val⟩⟩, ?_⟩
  · rw [← ht, ← Category.assoc, hφ, Category.assoc]
  · intro hsc
    let : IsSeparated G.X.hom := inferInstance
    let d := isSplitTorus_gm.dominantFactorization χ
    refine splitTorusCentralizerDerivedSimplyConnected k G hsc d.image d.inclusion
      d.isSplitSubtorus M j ?_ D i hi
    rw [← dynamicCentralizer_eq_torusCentralizer_image χ d]
    exact hj

/-- The derived subgroup of the centralizer of a dominant cocharacter has
the based root datum of its zero face. -/
def StandardLeviDerivedPinningStatement : Prop :=
  ∀ (k : Type u) [Field k] (G M D : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
      (p : SplitPinning G) (ν : cocharacterLattice p.torus),
      (∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν) →
      ∀ (j : M ⟶ G), (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ p.inclusion)).IsRepresentedBy j →
        ∀ (i : D ⟶ M), IsDerivedSubgroup i →
          Nonempty (StandardLeviDerivedPinning p ν j i) ∧ (IsSimplyConnected G → IsSimplyConnected D)

theorem standardLeviDerivedPinning : StandardLeviDerivedPinningStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ p ν hν j hj i hi => p.standardLeviDerivedPinning ν hν j hj i hi

end Langlands.GroupScheme
