import Langlands.GroupScheme.Rational.QuasiSplitRootRestriction
import Langlands.GroupScheme.Rational.TorusCentralizerQuasiSplit
import Langlands.GroupScheme.Reductive.TitsKernelIndexData
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Rational.RootFixedTorusSplitting
import Langlands.GroupScheme.Torus.AbsoluteCharacterIsomorphism
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Quasi-splitness and the marking of every Tits vertex -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.LinearAlgebra.RootDatumZeroFace

namespace Langlands.GroupScheme.TitsIndexData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- In the quasi-split case every vertex of the actual Tits index is distinguished. -/
theorem mem_distinguishedVertices_of_quasiSplit (hG : IsQuasiSplit G) (a : d.Vertex) :
    a ∈ d.distinguishedVertices := by
  intro hzero
  refine hG.root_restrict_ne_zero d.splitInclusion d.pinning.inclusion d.torusMap
    d.maximalSplit d.maximalTorus d.square d.pinning.isSplitTorus ?_
    ((d.rootRestriction_eq_zero_iff a.val).mp hzero)
  rw [← d.pinning.isRootDatum.2.1]
  exact Set.mem_range_self a.val

private theorem kernelCoweight_regular
    (hd : ∀ a : d.Vertex, a ∈ d.distinguishedVertices) (a : d.pinning.rootIndex) :
    d.pinning.rootDatum.root' a d.kernelCoweight ≠ 0 := by
  let p := d.pinning.rootDatum
  let f := p.toLinearMap.flip d.kernelCoweight
  have hs (i : d.pinning.rootIndex) (hi : i ∈ d.pinning.base.support) : f (p.root i) ≠ 0 := by
    intro hz
    exact hd ⟨i, hi⟩ ((d.rootRestriction_eq_zero_iff_root' i).mpr hz)
  have hpos (i : d.pinning.rootIndex) (hi : i ∈ d.pinning.base.support) : 0 < f (p.root i) :=
    (d.sign_kernelCoweight i (hs i hi)).mp (d.pinning.base.isPos_of_mem_support hi)
  have he : {i | i ∈ (d.pinning.base.support : Set d.pinning.rootIndex) ∧ f (p.root i) = 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun i hi => hs i hi.1 hi.2
  have hz (x : _) (hx : x ∈ AddSubmonoid.closure (p.root '' d.pinning.base.support))
      (hf : f x = 0) : x = 0 := by
    have h := mem_closure_zero_of_mem_closure_nonneg p.root _ f (fun i hi => (hpos i hi).le) hx hf
    simpa only [he, Set.image_empty, AddSubmonoid.closure_empty, AddSubmonoid.mem_bot] using h
  intro h
  change f (p.root a) = 0 at h
  rcases d.pinning.base.root_mem_or_neg_mem a with hp | hp
  · exact p.ne_zero a (hz _ hp h)
  · exact p.ne_zero a (neg_eq_zero.mp (hz _ hp (by rw [map_neg, h, neg_zero])))

/-- If all vertices are distinguished, the maximal split torus has a torus
as its full centralizer, so the group is quasi-split. -/
theorem isQuasiSplit_of_all_vertices_distinguished
    (hd : ∀ a : d.Vertex, a ∈ d.distinguishedVertices) : IsQuasiSplit G := by
  let K := SeparableClosure k
  let b := algebraBaseMap k K
  let t := d.pinning.inclusion
  let tK := (GroupScheme.baseChange b).map t
  let hG := d.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    d.pinning.isConnectedReductive.isAffineHom
  have hν : IsRegularCocharacter (T := (CommGroupScheme.baseChange b).obj d.pinning.torus)
      tK d.kernelCoweight := by
    intro α hα
    change α ∈ roots (T := (CommGroupScheme.baseChange b).obj d.pinning.torus) tK at hα
    rw [← d.pinning.isRootDatum.2.1] at hα
    obtain ⟨a, rfl⟩ := hα
    rw [← d.pinning.isRootDatum.1]
    exact d.kernelCoweight_regular hd a
  have hb : Dynamic.baseChangeCocharacter b
      (CommGroupScheme.groupHom d.positiveCocharacter ≫ d.splitInclusion) =
      CommGroupScheme.groupHom d.kernelCoweight ≫ tK := by
    rw [← d.square, ← Category.assoc]
    change Dynamic.baseChangeCocharacter b
      (CommGroupScheme.groupHom (d.positiveCocharacter ≫ d.torusMap) ≫ t) = _
    rw [Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic]
    rfl
  have hC : (torusCentralizer d.splitInclusion).baseChange b =
      (SubgroupFunctor.range t).baseChange b := by
    rw [← genericCentralizer k G hG d.splitTorus d.splitInclusion d.maximalSplit
      d.positiveCocharacter d.generic, ← Dynamic.centralizer_baseChange, hb,
      centralizer_comp_eq_range_of_isRegular d.pinning.isConnectedReductive d.pinning.isSplitTorus
        tK d.pinning.isMaximalTorus _ hν, SubgroupFunctor.range_baseChangeHom]
  have : IsClosedImmersion t.hom.hom.left := d.maximalTorus.2.1
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  obtain ⟨hbs, hbf, hbq⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbs
  let : Flat b := hbf
  let : QuasiCompact b := hbq
  have hD : torusCentralizer d.splitInclusion = SubgroupFunctor.range t :=
    le_antisymm (SubgroupFunctor.le_range_of_baseChange_le b t hC.le)
      d.range_inclusion_le_torusCentralizer
  exact d.maximalSplit.1.1.isQuasiSplit_of_torusCentralizer hG d.splitInclusion t
    ⟨inferInstance, hD.symm⟩ d.maximalTorus.1

/-- If the group is quasi-split and every simple vertex is fixed, then
the maximal torus in the actual index is split over the base field. -/
theorem isSplitTorus_of_quasiSplit_trivialStar (hG : IsQuasiSplit G)
    (hstar : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex),
      d.star σ a = a) : IsSplitTorus d.pinning.torus.toGrp := by
  let K := SeparableClosure k
  let b := algebraBaseMap k K
  let p := d.pinning
  let TK := (CommGroupScheme.baseChange b).obj p.torus
  let GK := (GroupScheme.baseChange b).obj G
  let : IsAffineHom GK.X.hom := p.isConnectedReductive.isAffineHom
  have hGK : IsSemisimple GK := d.isSemisimple.baseChange_of_algebraicExtension (K := K)
  have hreg := d.kernelCoweight_regular (d.mem_distinguishedVertices_of_quasiSplit hG)
  have hOrd (σ : K ≃ₐ[k] K) : (p.starAction σ).val = p.galoisAction σ := by
    apply p.starAction_eq_galoisAction
    apply based_of_isPos p.base (p.galoisAction σ)
    intro a
    rw [d.sign_kernelCoweight _ (hreg _), d.sign_kernelCoweight _ (hreg _)]
    exact Iff.of_eq (congrArg (fun z : ℤ => 0 < z) (d.root'_galoisAction σ a))
  have hfix (σ : K ≃ₐ[k] K) (χ : characterLattice TK) :
      characterLattice.galoisRepresentation k K p.torus σ χ = χ := by
    apply hGK.character_eq_of_fixed_roots p.isSplitTorus p.isMaximalTorus.2.1 p.isRootDatum
    intro α hα
    rw [← p.isRootDatum.2.1] at hα
    obtain ⟨i, rfl⟩ := hα
    obtain ⟨m, _, _, hm⟩ := p.base.exists_root_eq_sum_int i
    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_zsmul, ← StarActionIndependence.galoisAction_weightMap_apply, ← hOrd σ]
    let P := p.toSplitPinning.rootDatum
    have he : (p.starAction σ).val.indexEquiv a = a := congrArg Subtype.val (hstar σ ⟨a, ha⟩)
    exact congrArg (fun x => m a • x) (((p.starAction σ).val.root_weightMap_apply P P a).trans
      (congrArg P.root he))
  obtain ⟨I, hI, ⟨e⟩⟩ := p.isSplitTorus
  let S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  let hS : IsSplitTorus S.toGrp := isSplitTorus_splitTorus I
  let eK : TK ≅ (CommGroupScheme.baseChange b).obj S :=
    CommGroupScheme.isoOfGroupIso (e ≪≫ (splitTorus.baseChangeIso b I).symm)
  let : Module ℤ (characterLattice ((CommGroupScheme.baseChange b).obj S)) :=
    AddCommGroup.toIntModule _
  let : Module ℤ (characterLattice TK) := AddCommGroup.toIntModule _
  let f : characterLattice ((CommGroupScheme.baseChange b).obj S) ≃ₗ[ℤ] characterLattice TK :=
    (characterLattice.congr eK).symm.toIntLinearEquiv
  have hf (σ : K ≃ₐ[k] K) (χ : characterLattice ((CommGroupScheme.baseChange b).obj S)) :
      f (characterLattice.galoisRepresentation k K S σ χ) =
        characterLattice.galoisRepresentation k K p.torus σ (f χ) := by
    rw [hfix]
    obtain ⟨x, rfl⟩ := (hS.characterLattice_baseChange_bijective b S).surjective χ
    rw [characterLattice.galoisRepresentation_baseChange]
  let j := characterLattice.isoOfEquivariantAbsoluteEquiv hS.isTorus.isMultiplicativeType
    d.maximalTorus.1.isMultiplicativeType f hf
  let jG : p.torus.toGrp ≅ S.toGrp :=
    ⟨CommGroupScheme.groupHom j.hom, CommGroupScheme.groupHom j.inv,
      congrArg CommGroupScheme.groupHom j.hom_inv_id,
      congrArg CommGroupScheme.groupHom j.inv_hom_id⟩
  exact IsSplitTorus.of_iso jG hS

end Langlands.GroupScheme.TitsIndexData
