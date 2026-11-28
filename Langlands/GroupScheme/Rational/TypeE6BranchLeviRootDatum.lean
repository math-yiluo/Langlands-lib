import Langlands.GroupScheme.Rational.TypeE6BranchCocharacter
import Langlands.GroupScheme.Reductive.TitsKernelIndexData
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The based root datum of the derived E6 branch Levi -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LinearAlgebra.RootDatumZeroFace

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "E" => SeparableClosure k
local notation "b" => algebraBaseMap k (SeparableClosure k)
local notation "BG" => GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))

private theorem typeE6BranchCoweight_sign (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hCartan : ∀ x y, d.cartan x y = CartanMatrix.E 6 (e x) (e y))
    (a : d.pinning.rootIndex) (ha : d.pinning.rootDatum.root' a (d.typeE6BranchCoweight e) ≠ 0) :
    d.pinning.base.IsPos a ↔ 0 < d.pinning.rootDatum.root' a (d.typeE6BranchCoweight e) := by
  let P := d.pinning.rootDatum
  let F := P.toLinearMap.flip (d.typeE6BranchCoweight e)
  have hnonneg (x) (hx : x ∈ AddSubmonoid.closure (P.root '' d.pinning.base.support)) :
      0 ≤ F x := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      change 0 ≤ P.root' j (d.typeE6BranchCoweight e)
      rw [d.typeE6BranchCoweight_pairing e hCartan ⟨j, hj⟩]
      split <;> decide
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
  constructor
  · intro hp
    exact lt_of_le_of_ne (hnonneg _ ((isPos_iff_mem_closure _ a).mp hp)) (Ne.symm ha)
  · intro hp
    by_contra hn
    have hz := hnonneg _ ((neg_mem_closure_iff_not_isPos _ a).mpr hn)
    rw [map_neg] at hz
    exact (not_lt_of_ge (neg_nonneg.mp hz)) hp

variable [IsAffineHom D.X.hom]

/-- The torus and the simple roots in the actual derived group of a branch
centralizer can be chosen to match the zero face of the original E6 coweight. -/
structure TypeE6BranchDerivedPinning (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (i : D ⟶ M) where
  centralizerTorus : d.pinning.torus.toGrp ⟶ M
  centralizerTorus_maximal : IsMaximalTorus centralizerTorus
  pinning : GaloisPinningData k E D
  torusMap : pinning.torus ⟶ d.pinning.torus
  square : CommGroupScheme.groupHom torusMap ≫ centralizerTorus = pinning.inclusion ≫ i
  vertices : pinning.base.support ≃ {a : d.Vertex // e a ≠ 1}
  cartan_eq : ∀ a c : pinning.base.support,
    pinning.rootDatum.pairing a.val c.val = d.cartan (vertices a).val (vertices c).val
  coroot_eq : ∀ a : pinning.base.support,
    pinning.rootDatum.coroot a.val ≫ (BC).map torusMap =
      d.pinning.rootDatum.coroot (vertices a).val.val

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_typeE6BranchDerivedPinning
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hCartan : ∀ x y, d.cartan x y = CartanMatrix.E 6 (e x) (e y))
    (ν : cocharacterLattice d.splitTorus)
    (hν : cocharacterLattice.baseChange b d.pinning.torus (ν ≫ d.torusMap) =
      d.typeE6BranchCoweight e)
    (j : M ⟶ G) (hj : (torusCentralizer
      (CommGroupScheme.groupHom ν ≫ d.splitInclusion)).IsRepresentedBy j)
    (hM : IsConnectedReductive M) (i : D ⟶ M) (hi : IsDerivedSubgroup i) :
    Nonempty (TypeE6BranchDerivedPinning d e i) := by
  let c : cocharacterLattice d.pinning.torus := ν ≫ d.torusMap
  let χ := CommGroupScheme.groupHom ν ≫ d.splitInclusion
  have hc : CommGroupScheme.groupHom c ≫ d.pinning.inclusion = χ := by
    change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom d.torusMap) ≫
      d.pinning.inclusion = _
    rw [Category.assoc, d.square]
  let t := hj.liftOfLE d.pinning.inclusion
    (range_le_torusCentralizer_of_factor χ d.pinning.inclusion (CommGroupScheme.groupHom c) hc)
  have ht : t ≫ j = d.pinning.inclusion := hj.liftOfLE_comp _ _
  have hjc : IsClosedSubgroup j := isSplitTorus_gm.isClosedSubgroup_torusCentralizer χ hj
  have htmax : IsMaximalTorus t := IsMaximalTorus.of_comp hjc (ht.symm ▸ d.maximalTorus)
  let : IsClosedImmersion i.hom.hom.left := hi.1
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let T := commutativeSubgroupIntersection t i
  let u : T.toGrp ⟶ D := commutativeSubgroupIntersectionSnd t i
  let τ : T ⟶ d.pinning.torus := Additive.ofMul (commutativeSubgroupIntersectionFst t i)
  have hτ : CommGroupScheme.groupHom τ ≫ t = u ≫ i :=
    commutativeSubgroupIntersection_condition t i
  have hτc : IsClosedSubgroup (CommGroupScheme.groupHom τ) :=
    isClosedSubgroup_commutativeSubgroupIntersectionFst t i hi.1
  have humax : IsMaximalTorus u :=
    isMaximalTorus_commutativeSubgroupIntersectionSnd_derived hM i hi t htmax
  have hD := hi.isConnectedReductive hM
  let : Smooth D.X.hom := hD.smooth
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  have hDE := hD.baseChange_of_algebraicExtension (K := E)
  have hME := hM.baseChange_of_algebraicExtension (K := E)
  let : IsAffineHom ((BG).obj G).X.hom := d.pinning.isConnectedReductive.isAffineHom
  let : Smooth ((BG).obj G).X.hom := d.pinning.isConnectedReductive.smooth
  let : IsAffineHom ((BG).obj D).X.hom := hDE.isAffineHom
  let : Smooth ((BG).obj D).X.hom := hDE.smooth
  have hTE : IsSplitTorus ((BC).obj T).toGrp := isSplitTorus_baseChange_separableClosure humax.1
  have huE : IsMaximalTorus (T := (BC).obj T) ((BG).map u) :=
    (maximalTorusBaseChange k E D T u humax.1 humax.2.1).mp humax
  have htE : IsMaximalTorus (T := (BC).obj d.pinning.torus) ((BG).map t) :=
    (maximalTorusBaseChange k E M d.pinning.torus t htmax.1 htmax.2.1).mp htmax
  have hiE := hi.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b M)
  have hjE : (torusCentralizer (T := (BC).obj (Gm _)) ((BG).map χ)).IsRepresentedBy ((BG).map j) := by
    rw [torusCentralizer_baseChange]
    exact hj.baseChange b
  obtain ⟨K, hK, Q, hQ, hQred⟩ :=
    rootDatumExistence E ((BG).obj D) hDE ((BC).obj T) hTE ((BG).map u) huE
  let : Finite K := hK
  let τE := (BC).map τ
  let cE := (BC).map c
  obtain ⟨w, hw⟩ := exists_derivedCentralizerRootEquiv
    (T := (BC).obj d.pinning.torus) (A := (BC).obj (Gm _)) (TD := (BC).obj T)
    ((BG).map χ) ((isSplitTorus_gm (S := Spec (CommRingCat.of k))).baseChange b)
    ((BG).map j) hjE hME ((BG).map d.pinning.inclusion) d.pinning.isSplitTorus
    d.pinning.isRootDatum ((BG).map t) (by rw [← Functor.map_comp, ht]) htE
    cE (by rw [← hc, Functor.map_comp]; rfl) ((BG).map i) hiE ((BG).map u) hTE huE
    τE (by rw [← Functor.map_comp, ← hτ, Functor.map_comp]; rfl) hQ
  have hzero (a : d.pinning.rootIndex) :
      cE ≫ d.pinning.rootDatum.root a = 0 ↔
        d.pinning.rootDatum.root' a (d.typeE6BranchCoweight e) = 0 := by
    change _ ↔ d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a) _ = _
    rw [d.pinning.isRootDatum.1, latticePairing_apply, ← hν]
    change _ ↔ gmEndEquiv E (((Gm.commBaseChangeIso b).inv ≫ cE) ≫ d.pinning.rootDatum.root a) = 0
    rw [AddEquiv.map_eq_zero_iff, Category.assoc]
    exact ⟨fun h => by rw [h, comp_zero],
      fun h => (cancel_epi (Gm.commBaseChangeIso b).inv).mp (by rw [comp_zero]; exact h)⟩
  let : Mono (CommGroupScheme.groupHom τE).hom.hom.left := (hτc.baseChange b).mono
  let F : FaceDatum d.pinning.rootDatum d.pinning.base (d.typeE6BranchCoweight e) Q :=
    { sign := typeE6BranchCoweight_sign d e hCartan
      weightMap := characterPrecompInt τE
      coweightMap := RealTorusSpace.cocharacterMapInt τE
      coweightMap_injective := RealTorusSpace.cocharacterMapInt_injective _
      pairing_comm := fun x y => by rw [hQ.1, d.pinning.isRootDatum.1]; exact latticePairing_precomp _ _ _
      indexEquiv := w.trans (Equiv.subtypeEquivRight hzero)
      root_eq := fun q => (hw q).1
      coroot_eq := fun q => (hw q).2 }
  let p : GaloisPinningData k E D :=
    { torus := T
      inclusion := u
      isConnectedReductive := hDE
      isSplitTorus := hTE
      isMaximalTorus := huE
      rootIndex := K
      rootDatum := Q
      isRootDatum := hQ
      isReduced := hQred
      base := F.base
      pinning := RootPinning.ofSplitMaximalTorus hDE hTE _ huE Q hQ F.base }
  have hz (a : d.Vertex) :
      d.pinning.rootDatum.root' a.val (d.typeE6BranchCoweight e) = 0 ↔ e a ≠ 1 := by
    rw [d.typeE6BranchCoweight_pairing e hCartan]
    split <;> simp_all
  let v : p.base.support ≃ {a : d.Vertex // e a ≠ 1} :=
    { toFun := fun q => ⟨⟨(F.indexEquiv q.val).val, (F.mem_base_support q.val).mp q.property⟩,
        (hz _).mp (F.root'_index q.val)⟩
      invFun := fun a => ⟨F.indexEquiv.symm ⟨a.val.val, (hz a.val).mpr a.property⟩,
        (F.mem_base_support _).mpr (by rw [Equiv.apply_symm_apply]; exact a.val.property)⟩
      left_inv := fun q => Subtype.ext (F.indexEquiv.symm_apply_apply q.val)
      right_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        change (F.indexEquiv (F.indexEquiv.symm ⟨a.val.val, (hz a.val).mpr a.property⟩)).val = a.val.val
        rw [Equiv.apply_symm_apply] }
  exact ⟨⟨t, htmax, p, τ, hτ, v, fun a c => F.pairing_eq a.val c.val,
    fun a => F.coroot_eq a.val⟩⟩

/-- Over a field with algebraically closed separable closure, the complement of
the short-arm vertex gives A5 in any actual Tits index of the affine,
locally finite-type derived group. -/
theorem TypeE6BranchDerivedPinning.exists_typeA5_numbering
    [LocallyOfFiniteType D.X.hom] [IsAlgClosed E]
    {d : TitsIndexData G} {e : d.Vertex ≃ Fin 6} {i : D ⟶ M}
    (p : TypeE6BranchDerivedPinning d e i)
    (hCartan : ∀ x y, d.cartan x y = CartanMatrix.E 6 (e x) (e y))
    (dD : TitsIndexData D) :
    ∃ eD : dD.Vertex ≃ Fin 5,
      ∀ a c, dD.cartan a c = CartanMatrix.A 5 (eD a) (eD c) := by
  let : IsAffineHom ((BG).obj D).X.hom := p.pinning.isConnectedReductive.isAffineHom
  obtain ⟨_, _, r, _, _, hbase⟩ := StarActionIndependence.exists_conj_based
    dD.pinning.toSplitPinning p.pinning.toSplitPinning
  let v : dD.Vertex ≃ p.pinning.base.support := r.indexEquiv.subtypeEquiv hbase
  let w : dD.Vertex ≃ {x : Fin 6 // x ≠ 1} :=
    v.trans (p.vertices.trans (e.subtypeEquiv fun _ => Iff.rfl))
  let eD : dD.Vertex ≃ Fin 5 := w.trans (finSuccAboveEquiv (1 : Fin 6)).symm
  have hw (a : dD.Vertex) : e (p.vertices (v a)).val = (1 : Fin 6).succAbove (eD a) :=
    (congrArg (fun j : {x : Fin 6 // x ≠ 1} => j.val)
      ((finSuccAboveEquiv (1 : Fin 6)).apply_symm_apply (w a))).symm
  have hA : ∀ a c : Fin 5,
      CartanMatrix.E 6 ((1 : Fin 6).succAbove a) ((1 : Fin 6).succAbove c) =
        CartanMatrix.A 5 a c := by
    simp only [CartanMatrix.E, CartanMatrix.A, Matrix.of_apply]
    decide
  refine ⟨eD, fun a c => ?_⟩
  have h : p.pinning.rootDatum.pairing (v a).val (v c).val = dD.cartan a c := r.toHom.pairing
  rw [← h, p.cartan_eq, hCartan, hw, hw]
  exact hA _ _

end Langlands.GroupScheme
