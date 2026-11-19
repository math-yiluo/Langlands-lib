import Langlands.GroupScheme.Reductive.SplitLeviTitsComparison
import Langlands.GroupScheme.Reductive.GaloisPinningBaseChange
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleRestriction

/-! # Base change of Levi comparison data to an intermediate field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (E : Type u) [Field E] [Algebra k E] [Algebra E K] [IsScalarTower k E K]
  {G D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom D.X.hom]
  {d : GaloisPinningData k K G}

/-- The base change of a split torus datum to an intermediate field `E`. -/
def SplitTorusDatum.baseChange (s : d.SplitTorusDatum) : (d.baseChange E).SplitTorusDatum where
  splitTorus := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj s.splitTorus
  splitInclusion := (GroupScheme.baseChange (algebraBaseMap k E)).map s.splitInclusion
  isSplitTorus := s.isSplitTorus.baseChange _
  torusMap := (CommGroupScheme.baseChange (algebraBaseMap k E)).map s.torusMap
  square := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map
        (CommGroupScheme.groupHom s.torusMap) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion = _
    rw [← Functor.map_comp, s.square]
  positiveCocharacter :=
    cocharacterLattice.baseChange (algebraBaseMap k E) s.splitTorus s.positiveCocharacter

/-- Restriction to the base-changed split torus of a transported weight is the base change of
the restriction. -/
theorem SplitTorusDatum.baseChange_restriction (s : d.SplitTorusDatum)
    (x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus)) :
    (s.baseChange E).restriction (d.weightTransport E x) =
      characterLattice.baseChange (algebraBaseMap k E) s.splitTorus (s.restriction x) := by
  set y := s.restriction x with hy_def
  have hy : (CommGroupScheme.baseChange (algebraBaseMap k K)).map s.torusMap ≫ x =
      characterLattice.baseChange (algebraBaseMap k K) s.splitTorus y :=
    ((characterLattice.baseChangeEquiv (algebraBaseMap k K) s.splitTorus
      s.isSplitTorus).apply_symm_apply _).symm
  have h1 : (CommGroupScheme.baseChange (algebraBaseMap E K)).map
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map s.torusMap) ≫
        d.weightTransport E x =
      characterTowerEquiv k E K s.splitTorus
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).map s.torusMap ≫ x) :=
    (characterTowerEquiv_comp k E K s.torusMap x).symm
  have h2 : characterTowerEquiv k E K s.splitTorus
      (characterLattice.baseChange (algebraBaseMap k K) s.splitTorus y) =
      characterLattice.baseChange (algebraBaseMap E K) _
        (characterLattice.baseChange (algebraBaseMap k E) s.splitTorus y) := by
    rw [characterTowerEquiv_apply, ← StarActionFiniteStage.towerCharacterOf_baseChange
      (algebraBaseMap k E) (algebraBaseMap E K) (algebraBaseMap k K)
      (algebraBaseMap_comp_algebraBaseMap k E K) s.splitTorus y]
    unfold StarActionFiniteStage.towerCharacterOf torusTowerIso
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (characterLattice.baseChangeEquiv (algebraBaseMap E K) _
    (s.baseChange E).isSplitTorus).symm
      ((CommGroupScheme.baseChange (algebraBaseMap E K)).map
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map s.torusMap) ≫
        d.weightTransport E x) = _
  rw [h1, hy, h2]
  exact (characterLattice.baseChangeEquiv (algebraBaseMap E K) _
    (s.baseChange E).isSplitTorus).symm_apply_apply _

theorem SplitTorusDatum.baseChange_restriction_root_eq_zero_iff (s : d.SplitTorusDatum)
    (a : d.rootIndex) :
    (s.baseChange E).restriction ((d.baseChange E).rootDatum.root a) = 0 ↔
      s.restriction (d.rootDatum.root a) = 0 := by
  have h := s.baseChange_restriction E (d.rootDatum.root a)
  change (s.baseChange E).restriction (d.weightTransport E (d.rootDatum.root a)) = 0 ↔ _
  rw [h]
  constructor
  · intro h0
    apply characterLattice.baseChange_injective (algebraBaseMap k E) s.splitTorus
    rw [h0, map_zero]
  · intro h0
    rw [h0, map_zero]

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType D.X.hom]

omit [LocallyOfFiniteType D.X.hom] [IsAffineHom D.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- The star action of `σ ∈ Gal(K/E)` on the simple vertices of the base change is the star
action of `σ` viewed in `Gal(K/k)`. -/
theorem baseChange_vertexStar {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] {d' : GaloisPinningData k K H} (σ : K ≃ₐ[E] K)
    (a : (d'.baseChange E).base.support) :
    ((d'.baseChange E).vertexStar σ a).val =
      (d'.starAction (σ.restrictScalars k)).val.indexEquiv a.val := by
  have h := congrArg (fun f => f.indexEquiv a.val)
    (d'.baseChangeRootDatumEquiv_comp_starAction E σ)
  exact h.symm

variable {s : d.SplitTorusDatum} {ι : D ⟶ G} {e : GaloisPinningData k K D}

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType D.X.hom] [IsAffineHom G.X.hom]
  [IsAffineHom D.X.hom] in
theorem mem_baseChange_support {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    {d' : GaloisPinningData k K H} (a : d'.rootIndex) :
    a ∈ (d'.baseChange E).base.support ↔ a ∈ d'.base.support := by
  change a ∈ (d'.baseChange E).toSplitPinning.base.support ↔ a ∈ d'.toSplitPinning.base.support
  rw [d'.baseChange_base_support E]

/-- The correspondence of simple vertices after base change. -/
def LeviComparison.baseChangeVertexEquiv (L : d.LeviComparison s ι e) :
    (e.baseChange E).base.support ≃ (s.baseChange E).zeroVertex where
  toFun b := ⟨⟨(L.vertexEquiv ⟨b.val, (mem_baseChange_support (d' := e) E b.val).mp
      b.property⟩).val.val,
      (mem_baseChange_support (d' := d) E _).mpr
        (L.vertexEquiv ⟨b.val, (mem_baseChange_support (d' := e) E b.val).mp
          b.property⟩).val.property⟩,
    (s.baseChange_restriction_root_eq_zero_iff E _).mpr
      (L.vertexEquiv ⟨b.val, (mem_baseChange_support (d' := e) E b.val).mp
        b.property⟩).property⟩
  invFun a := ⟨(L.vertexEquiv.symm ⟨⟨a.val.val, (mem_baseChange_support (d' := d) E _).mp
      a.val.property⟩, (s.baseChange_restriction_root_eq_zero_iff E _).mp a.property⟩).val,
    (mem_baseChange_support (d' := e) E _).mpr (L.vertexEquiv.symm ⟨⟨a.val.val,
      (mem_baseChange_support (d' := d) E _).mp a.val.property⟩,
      (s.baseChange_restriction_root_eq_zero_iff E _).mp a.property⟩).property⟩
  left_inv b := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]

theorem LeviComparison.baseChangeVertexEquiv_val (L : d.LeviComparison s ι e)
    (b : (e.baseChange E).base.support) :
    ((L.baseChangeVertexEquiv E b).val.val : d.rootIndex) =
      (L.vertexEquiv ⟨b.val, (mem_baseChange_support (d' := e) E b.val).mp
        b.property⟩).val.val := rfl

theorem LeviComparison.baseChange_root_eq (L : d.LeviComparison s ι e)
    (b : (e.baseChange E).base.support) :
    (CommGroupScheme.baseChange (algebraBaseMap E K)).map
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map L.kernelTorusMap) ≫
      d.weightTransport E (d.rootDatum.root (L.baseChangeVertexEquiv E b).val.val) =
      e.weightTransport E (e.rootDatum.root b.val) := by
  rw [LeviComparison.baseChangeVertexEquiv_val E L]
  have h := characterTowerEquiv_comp k E K L.kernelTorusMap
    (d.rootDatum.root (L.vertexEquiv ⟨b.val, (mem_baseChange_support (d' := e) E b.val).mp
      b.property⟩).val.val)
  rw [L.root_eq] at h
  exact h.symm

theorem LeviComparison.baseChange_coroot_eq (L : d.LeviComparison s ι e)
    (b : (e.baseChange E).base.support) :
    (e.rootDatum.coroot b.val ≫ (torusTowerIso k E K e.torus).hom) ≫
        (CommGroupScheme.baseChange (algebraBaseMap E K)).map
          ((CommGroupScheme.baseChange (algebraBaseMap k E)).map L.kernelTorusMap) =
      d.rootDatum.coroot (L.baseChangeVertexEquiv E b).val.val ≫
        (torusTowerIso k E K d.torus).hom := by
  rw [LeviComparison.baseChangeVertexEquiv_val E L, Category.assoc, ← torusTowerIso_hom_naturality,
    ← Category.assoc]
  exact congrArg (· ≫ (torusTowerIso k E K d.torus).hom)
    (L.coroot_eq ⟨b.val, (mem_baseChange_support (d' := e) E b.val).mp b.property⟩)

/-- The base change of Levi comparison data to an intermediate field `E`. The split torus need
not be maximal and the derived group need not be anisotropic after base change. -/
def LeviComparison.baseChange (L : d.LeviComparison s ι e) :
    (d.baseChange E).LeviComparison (s.baseChange E)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map ι) (e.baseChange E) where
  kernelTorusMap := (CommGroupScheme.baseChange (algebraBaseMap k E)).map L.kernelTorusMap
  kernelSquare := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map
        (CommGroupScheme.groupHom L.kernelTorusMap) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion =
      (GroupScheme.baseChange (algebraBaseMap k E)).map e.inclusion ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map ι
    rw [← Functor.map_comp, ← Functor.map_comp, L.kernelSquare]
  centralizes := L.centralizes_baseChange E
  vertexEquiv := L.baseChangeVertexEquiv E
  pos := fun a ha => by
    obtain ⟨a0, ha0⟩ := a
    have ha' : s.restriction (d.rootDatum.root a0) ≠ 0 := fun h0 =>
      ha ((s.baseChange_restriction_root_eq_zero_iff E a0).mpr h0)
    have hpos := L.pos ⟨a0, (mem_baseChange_support (d' := d) E a0).mp ha0⟩ ha'
    have key := s.baseChange_restriction E (d.rootDatum.root a0)
    have hpair := latticePairing_baseChange (algebraBaseMap k E) s.splitTorus
      (s.restriction (d.rootDatum.root a0)) s.positiveCocharacter
    calc (0 : ℤ) < latticePairing s.splitTorus (s.restriction (d.rootDatum.root a0))
          s.positiveCocharacter := hpos
      _ = latticePairing (s.baseChange E).splitTorus
          ((s.baseChange E).restriction (d.weightTransport E (d.rootDatum.root a0)))
          (s.baseChange E).positiveCocharacter := by rw [key]; exact hpair.symm
  root_eq := L.baseChange_root_eq E
  coroot_eq := L.baseChange_coroot_eq E
  star_eq := fun σ b => by
    have hb : b.val ∈ e.base.support := (mem_baseChange_support (d' := e) E b.val).mp b.property
    have he : (⟨((e.baseChange E).vertexStar σ b).val,
        (mem_baseChange_support (d' := e) E _).mp ((e.baseChange E).vertexStar σ b).property⟩ :
          e.base.support) = e.vertexStar (σ.restrictScalars k) ⟨b.val, hb⟩ :=
      Subtype.ext (baseChange_vertexStar E σ b)
    have hL := L.star_eq (σ.restrictScalars k) ⟨b.val, hb⟩
    apply Subtype.ext
    rw [baseChange_vertexStar, LeviComparison.baseChangeVertexEquiv_val E L, LeviComparison.baseChangeVertexEquiv_val E L, he,
      hL]
    rfl

/-- Restriction after base change, applied to transported weights, is the transport of the
original restriction. -/
theorem LeviComparison.baseChange_weightRestriction (L : d.LeviComparison s ι e)
    (x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus)) :
    (L.baseChange E).weightRestriction (d.weightTransport E x) =
      e.weightTransport E (L.weightRestriction x) :=
  (characterTowerEquiv_comp k E K L.kernelTorusMap x).symm

/-- Clause 4 for Levi comparison data: after base change to an intermediate field `E` with
`K/E` Galois, the actual Tits obstruction of `G_E` is the actual Tits obstruction of `D_E`
composed with restriction of star-fixed weights. -/
theorem LeviComparison.baseChange_titsObstruction [IsGalois E K] (L : d.LeviComparison s ι e)
    (hG : IsSimplyConnected G) (hD : IsSimplyConnected D) :
    ((e.baseChange E).titsObstruction (isSimplyConnectedFieldExtension k E D hD)).comp
        ((L.baseChange E).starFixedRestriction
          ((e.baseChange E).corootSpan_eq_top_of_simplyConnected
            (isSimplyConnectedFieldExtension k E D hD))) =
      (d.baseChange E).titsObstruction (isSimplyConnectedFieldExtension k E G hG) :=
  (L.baseChange E).titsObstruction_comp_starFixedRestriction _ _

end Langlands.GroupScheme.GaloisPinningData

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G}

/-- Clause 4: for every intermediate field `E` of `K/k` (`K` the separable closure) and every
weight `λ` of the base change `G_E` fixed by the full star action of `Gal(K/E)`, the actual
Tits obstruction of `G_E` at `λ` is the actual Tits obstruction of the base change `H_E` of
the actual anisotropic kernel at the restriction of `λ`. Neither maximality of the base change
of the split torus nor anisotropy of `H_E` is used. -/
theorem baseChange_titsObstruction_eq (p : d.AnisotropicKernelIndex) (hG : IsSimplyConnected G)
    (E : IntermediateField k (SeparableClosure k))
    (lam : (d.pinning.baseChange E).starFixedWeights) :
    (d.pinning.baseChange E).titsObstruction (isSimplyConnectedFieldExtension k E G hG) lam =
      (p.index.pinning.baseChange E).titsObstruction
        (isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hG))
        ((p.leviComparison.baseChange E).starFixedRestriction
          ((p.index.pinning.baseChange E).corootSpan_eq_top_of_simplyConnected
            (isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hG))) lam) :=
  (DFunLike.congr_fun (p.leviComparison.baseChange_titsObstruction E hG
    (p.isSimplyConnected hG)) lam).symm

/-- In clause 4, the restricted weight is the transport of the original restriction of `λ` to
the torus of the actual anisotropic kernel. -/
theorem baseChange_starFixedRestriction_val (p : d.AnisotropicKernelIndex)
    (hG : IsSimplyConnected G) (E : IntermediateField k (SeparableClosure k))
    (lam : (d.pinning.baseChange E).starFixedWeights)
    (x : characterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus))
    (hx : lam.1 = d.pinning.weightTransport E x) :
    (((p.leviComparison.baseChange E).starFixedRestriction
        ((p.index.pinning.baseChange E).corootSpan_eq_top_of_simplyConnected
          (isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hG))) lam) :
        characterLattice (p.index.pinning.baseChange E).toSplitPinning.torus) =
      p.index.pinning.weightTransport E (p.comparison.weightRestriction x) := by
  rw [GaloisPinningData.LeviComparison.starFixedRestriction_apply, hx]
  exact GaloisPinningData.LeviComparison.baseChange_weightRestriction E p.leviComparison x

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
