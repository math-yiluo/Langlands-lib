import Langlands.GroupScheme.Rational.GaloisBorelFaceDerived
import Langlands.GroupScheme.Reductive.TitsKernelIndexData

/-! # Absolute roots and coroots of a descended Levi derived group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RootDatumZeroFace

namespace Langlands.GroupScheme.GaloisBorelFaceDerived

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {p : GaloisPinningData F E G}

local notation "b" => algebraBaseMap F E
local notation "BG" => GroupScheme.baseChange b
local notation "BC" => CommGroupScheme.baseChange b
local notation "GE" => Functor.obj BG G
local notation "TE" => Functor.obj BC p.torus
local notation "tE" => CategoryTheory.Functor.map BG p.inclusion

variable {ν : cocharacterLattice
    ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj p.torus)}
  (L : GaloisBorelFaceDerived p ν)

local notation "ME" => Functor.obj BG L.levi
local notation "DE" => Functor.obj BG L.derived
local notation "TDE" => Functor.obj BC L.torus
local notation "tME" => CategoryTheory.Functor.map BG L.leviTorusInclusion
local notation "tDE" => CategoryTheory.Functor.map BG L.torusInclusion
local notation "τ" => CategoryTheory.Functor.map BC L.torusMap

omit [LocallyOfFiniteType G.X.hom] in
theorem derivedAffine : IsAffineHom L.derived.X.hom :=
  L.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom

omit [LocallyOfFiniteType G.X.hom] in
theorem derivedFiniteType : LocallyOfFiniteType L.derived.X.hom :=
  letI : Smooth L.derived.X.hom := L.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  inferInstance

omit [LocallyOfFiniteType G.X.hom] in
private theorem pairing_eq_zero_iff_restrict
    {A : CommGroupScheme (Spec (CommRingCat.of E))} (a : A.toGrp ⟶ GE)
    (hA : IsSplitTorus A.toGrp) (f : A ⟶ TE) (hf : CommGroupScheme.groupHom f ≫ tE = a)
    (ha : (torusCentralizer a).IsRepresentedBy ((BG).map L.inclusion))
    (i : p.rootIndex) :
    f ≫ p.rootDatum.root i = 0 ↔ latticePairing TE (p.rootDatum.root i) ν = 0 := by
  let : IsAffineHom (GE).X.hom := p.isConnectedReductive.isAffineHom
  let : Smooth (GE).X.hom := p.isConnectedReductive.smooth
  have hM := connectedReductiveFieldExtensionStatement F E L.levi L.isReductive
  let : IsAffineHom (ME).X.hom := hM.isAffineHom
  let : Smooth (ME).X.hom := hM.smooth
  have ht : tME ≫ (BG).map L.inclusion = tE := by
    rw [← Functor.map_comp, L.leviTorus_comp]
  have h₁ := relativeRoots_splitTorusCentralizer_factor (T := TE) a hA tE tME
    ((BG).map L.inclusion) ha ht f hf
  have h₂ := relativeRoots_centralizer_factor (T := TE) dynamicLie tE tME
    ((BG).map L.inclusion) ht ν L.isCentralizer
  have hr : p.rootDatum.root i ∈ relativeRoots tE := by
    rw [relativeRoots_eq_roots, ← p.isRootDatum.2.1]
    exact Set.mem_range_self i
  constructor
  · intro h
    have hm : p.rootDatum.root i ∈ relativeRoots tME := by rw [h₁]; exact ⟨hr, h⟩
    rw [h₂] at hm
    exact hm.2
  · intro h
    have hm : p.rootDatum.root i ∈ relativeRoots tME := by rw [h₂]; exact ⟨hr, h⟩
    rw [h₁] at hm
    exact hm.2

omit [LocallyOfFiniteType G.X.hom] in
local instance upperDerivedAffine : IsAffineHom (DE).X.hom := by
  let : IsAffineHom L.derived.X.hom := L.derivedAffine
  change IsAffineHom (CategoryTheory.Limits.pullback.snd L.derived.X.hom b)
  infer_instance

/-- The actual roots of the induced maximal torus match the ambient roots
with zero value on the defining cocharacter, with their exact coroot maps. -/
theorem exists_rootEquiv
    (hTD : IsSplitTorus (TDE).toGrp)
    {K : Type u} {Q : RootDatum K (characterLattice TDE) (cocharacterLattice TDE)}
    (hQ : IsRootDatumOf tDE Q) :
    ∃ φ : K ≃ {a : p.rootIndex // p.rootDatum.root' a ν = 0}, ∀ q,
      Q.root q = τ ≫ p.rootDatum.root (φ q) ∧
      Q.coroot q ≫ τ = p.rootDatum.coroot (φ q) := by
  let : IsAffineHom (GE).X.hom := p.isConnectedReductive.isAffineHom
  let : LocallyOfFiniteType (GE).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : IsAffineHom L.levi.X.hom := L.isReductive.isAffineHom
  let : IsAffineHom L.derived.X.hom := L.derivedAffine
  let : LocallyOfFiniteType L.derived.X.hom := L.derivedFiniteType
  let : LocallyOfFiniteType (DE).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd L.derived.X.hom b))
  let : Smooth L.levi.X.hom := L.isReductive.smooth
  let : Smooth L.derived.X.hom := L.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  let χ := CommGroupScheme.groupHom ν ≫ tE
  let a := isSplitTorus_gm.dominantFactorization χ
  have ha : (torusCentralizer a.inclusion).IsRepresentedBy ((BG).map L.inclusion) := by
    rw [← dynamicCentralizer_eq_torusCentralizer_image χ a]
    exact L.isCentralizer
  have hR : SubgroupFunctor.range χ ≤ SubgroupFunctor.range tE := SubgroupFunctor.range_comp_le _ _
  let f : a.image ⟶ TE := Additive.ofMul (a.closedFactor tE p.isMaximalTorus.2.1 hR)
  have hf : CommGroupScheme.groupHom f ≫ tE = a.inclusion :=
    a.closedFactor_comp tE p.isMaximalTorus.2.1 hR
  have hM := connectedReductiveFieldExtensionStatement F E L.levi L.isReductive
  have hd := L.isDerived.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b L.levi)
  have htM := L.leviTorus_maximal
  have htD := L.torus_maximal
  have hm : IsMaximalTorus (T := TE) tME :=
    (maximalTorusBaseChange F E L.levi p.torus _ htM.1 htM.2.1).mp htM
  have ht : tME ≫ (BG).map L.inclusion = tE := by
    rw [← Functor.map_comp, L.leviTorus_comp]
  have hds : IsMaximalTorus (T := TDE) tDE :=
    (maximalTorusBaseChange F E L.derived L.torus _ htD.1 htD.2.1).mp htD
  have hτ : tDE ≫ (BG).map L.derivedInclusion = CommGroupScheme.groupHom τ ≫ tME := by
    rw [← Functor.map_comp, L.torus_square, Functor.map_comp]
    rfl
  obtain ⟨φ, hφ⟩ := exists_derivedCentralizerRootEquiv (T := TE) (TD := TDE)
    a.inclusion a.isSplitSubtorus.1 ((BG).map L.inclusion) ha hM
    tE p.isSplitTorus p.isRootDatum tME ht hm f hf
    ((BG).map L.derivedInclusion) hd tDE hTD hds τ hτ hQ
  let eq : {i : p.rootIndex // f ≫ p.rootDatum.root i = 0} ≃
      {i : p.rootIndex // p.rootDatum.root' i ν = 0} :=
    Equiv.subtypeEquivRight fun i => by
      change f ≫ p.rootDatum.root i = 0 ↔ p.rootDatum.toLinearMap (p.rootDatum.root i) ν = 0
      rw [p.isRootDatum.1]
      exact L.pairing_eq_zero_iff_restrict a.inclusion a.isSplitSubtorus.1 f hf ha i
  exact ⟨φ.trans eq, hφ⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- A cocharacter with nonnegative simple-root values refines the signs
of the given base on the roots where it has nonzero value. -/
theorem isPos_iff_root'_pos_of_simple_nonneg
    (hν : ∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν)
    (i : p.rootIndex) (hi : p.rootDatum.root' i ν ≠ 0) :
    p.base.IsPos i ↔ 0 < p.rootDatum.root' i ν := by
  let f := p.rootDatum.toLinearMap.flip ν
  have hnonneg (x : characterLattice TE)
      (hx : x ∈ AddSubmonoid.closure (p.rootDatum.root '' p.base.support)) : 0 ≤ f x := by
    induction hx using AddSubmonoid.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact hν ⟨j, hj⟩
    | zero => simp
    | add x y _ _ hx hy => exact (map_add f x y).symm ▸ add_nonneg hx hy
  refine ⟨fun hp => lt_of_le_of_ne ?_ hi.symm, fun hp => by_contra fun hn => ?_⟩
  · exact hnonneg _ ((isPos_iff_mem_closure p.base i).mp hp)
  · have h := hnonneg _ ((neg_mem_closure_iff_not_isPos p.base i).mpr hn)
    rw [map_neg] at h
    exact (not_lt_of_ge (neg_nonneg.mp h)) hp

/-- The based zero face on the maximal torus of the actual derived group. -/
theorem exists_faceDatum
    (hTD : IsSplitTorus (TDE).toGrp)
    (hν : ∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν)
    {K : Type u} {Q : RootDatum K (characterLattice TDE) (cocharacterLattice TDE)}
    (hQ : IsRootDatumOf tDE Q) :
    ∃ f : FaceDatum p.rootDatum p.base ν Q,
      ∀ z, f.coweightMap z = z ≫ τ := by
  obtain ⟨φ, hφ⟩ := L.exists_rootEquiv hTD hQ
  let : Mono (CommGroupScheme.groupHom τ).hom.hom.left :=
    (L.torusMap_closed.baseChange b).mono
  exact ⟨{
    sign := isPos_iff_root'_pos_of_simple_nonneg (p := p) hν
    weightMap := characterPrecompInt τ
    coweightMap := RealTorusSpace.cocharacterMapInt τ
    coweightMap_injective := RealTorusSpace.cocharacterMapInt_injective _
    pairing_comm := fun x y => by rw [hQ.1, p.isRootDatum.1]; exact latticePairing_precomp _ _ _
    indexEquiv := φ
    root_eq := fun q => (hφ q).1
    coroot_eq := fun q => (hφ q).2 }, fun _ => rfl⟩

/-- The based root datum of a derived Levi, equipped with its actual integral
coroot comparison with the ambient maximal torus. -/
structure RootModel where
  isSplit : IsSplitTorus (TDE).toGrp
  rootIndex : Type u
  [finiteRootIndex : Finite rootIndex]
  rootDatum : RootDatum rootIndex (characterLattice TDE) (cocharacterLattice TDE)
  isRootDatum : IsRootDatumOf tDE rootDatum
  isReduced : rootDatum.IsReduced
  face : FaceDatum p.rootDatum p.base ν rootDatum
  coweightMap_eq : ∀ z, face.coweightMap z = z ≫ τ

attribute [instance] RootModel.finiteRootIndex

/-- Any nonnegative direction in the closure of the based chamber supplies
the induced based root datum. -/
theorem nonempty_rootModel
    (hTD : IsSplitTorus (TDE).toGrp)
    (hν : ∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν) :
    Nonempty (RootModel L) := by
  let : IsAffineHom L.derived.X.hom := L.derivedAffine
  let : Smooth L.derived.X.hom := L.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  have hD := connectedReductiveFieldExtensionStatement F E L.derived
    L.isSimplyConnected.isSemisimple.isConnectedReductive
  have h := L.torus_maximal
  have hmax := (maximalTorusBaseChange F E L.derived L.torus L.torusInclusion h.1 h.2.1).mp h
  obtain ⟨K, hK, Q, hQ, hred⟩ := rootDatumExistence E (DE) hD (TDE) hTD tDE hmax
  let : Finite K := hK
  obtain ⟨f, hf⟩ := L.exists_faceDatum hTD hν hQ
  exact ⟨⟨hTD, K, Q, hQ, hred, f, hf⟩⟩

namespace RootModel

variable {L} (R : RootModel L)

/-- The simple vertices of the derived group are precisely the chosen
zero face of the ambient simple vertices. -/
def simpleEquiv :
    R.face.base.support ≃ {a : p.base.support // p.rootDatum.root' a.val ν = 0} where
  toFun a := ⟨⟨R.face.indexEquiv a.val, (R.face.mem_base_support a.val).mp a.property⟩,
    R.face.root'_index a.val⟩
  invFun a := ⟨R.face.indexEquiv.symm ⟨a.val.val, a.property⟩, by
    apply (R.face.mem_base_support _).mpr
    simpa only [Equiv.apply_symm_apply] using a.val.property⟩
  left_inv a := Subtype.ext (R.face.indexEquiv.symm_apply_apply a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    change (R.face.indexEquiv (R.face.indexEquiv.symm ⟨a.val.val, a.property⟩)).val = a.val.val
    exact congrArg (fun q : {t : p.rootIndex // p.rootDatum.root' t ν = 0} => q.val)
      (R.face.indexEquiv.apply_symm_apply ⟨a.val.val, a.property⟩)

omit [LocallyOfFiniteType G.X.hom] in
@[simp] theorem simpleEquiv_val (a : R.face.base.support) :
    (R.simpleEquiv a).val.val = (R.face.indexEquiv a.val).val := rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- A derived simple coroot maps to its matching ambient simple coroot. -/
theorem coroot_comp_torusMap (a : R.face.base.support) :
    R.rootDatum.coroot a.val ≫ τ = p.rootDatum.coroot (R.simpleEquiv a).val.val :=
  (R.coweightMap_eq (R.rootDatum.coroot a.val)).symm.trans (R.face.coroot_eq a.val)

attribute [local instance] derivedAffine

/-- The Galois pinning with the inherited base, on the actual derived torus. -/
def pinning : GaloisPinningData F E L.derived := by
  let : Smooth L.derived.X.hom := L.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  have hD := connectedReductiveFieldExtensionStatement F E L.derived
    L.isSimplyConnected.isSemisimple.isConnectedReductive
  have h := L.torus_maximal
  have ht := (maximalTorusBaseChange F E L.derived L.torus L.torusInclusion h.1 h.2.1).mp h
  exact
    { torus := L.torus
      inclusion := L.torusInclusion
      isConnectedReductive := hD
      isSplitTorus := R.isSplit
      isMaximalTorus := ht
      rootIndex := R.rootIndex
      rootDatum := R.rootDatum
      isRootDatum := R.isRootDatum
      isReduced := R.isReduced
      base := R.face.base
      pinning := RootPinning.ofSplitMaximalTorus hD R.isSplit tDE ht
        R.rootDatum R.isRootDatum R.face.base }

end RootModel

end Langlands.GroupScheme.GaloisBorelFaceDerived
