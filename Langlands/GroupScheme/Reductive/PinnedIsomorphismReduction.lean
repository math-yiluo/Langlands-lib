import Langlands.GroupScheme.Reductive.PinningLattice
import Langlands.GroupScheme.Reductive.PinnedRigidityStatement
import Langlands.GroupScheme.Reductive.PinnedRootScalingStatement
import Langlands.GroupScheme.Reductive.SplitIsomorphismStatement
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport

/-! # Reduction of the pinned Isomorphism Theorem to three prerequisites -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Transport

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  {J J' : Type*}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
  {j : T'.toGrp ⟶ H}

/-- The underlying isomorphism of group schemes of an isomorphism of commutative
group schemes. -/
private def torusGroupIso (t : T ≅ T') : T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom t.hom
  inv := CommGroupScheme.groupHom t.inv
  hom_inv_id := congrArg Additive.toMul t.hom_inv_id
  inv_hom_id := congrArg Additive.toMul t.inv_hom_id

omit [IsAffineHom H.X.hom] in
private theorem precomp_square (t : T ≅ T') :
    j ≫ (Iso.refl H).hom = CommGroupScheme.groupHom t.symm.hom ≫
      (CommGroupScheme.groupHom t.hom ≫ j) := by
  rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
  change j = CommGroupScheme.groupHom (t.inv ≫ t.hom) ≫ j
  rw [Iso.inv_hom_id]
  exact (Category.id_comp j).symm

/-- Precomposing a torus embedding with a torus isomorphism `t` transports a root
datum `Q` of the embedding to any root datum `P` with the actual pairing that is
equivalent to `Q` through a root-datum equivalence whose weight map is
`characterLattice.congr t`. -/
theorem IsRootDatumOf.precomp_torusIso (t : T ≅ T') (hQ : IsRootDatumOf j Q)
    (hP : P.toLinearMap = latticePairing T) (e : RootPairing.Equiv P Q)
    (he : ∀ χ, e.weightEquiv χ = characterLattice.congr t χ) :
    IsRootDatumOf (CommGroupScheme.groupHom t.hom ≫ j) P := by
  have hroot : ∀ a, characterLattice.congr t (P.root a) = Q.root (e.indexEquiv a) :=
    fun a => (he _).symm.trans (e.root_weightMap_apply P Q a)
  have hrefl : ∀ a χ, characterLattice.congr t (P.reflection a χ) =
      Q.reflection (e.indexEquiv a) (characterLattice.congr t χ) := by
    intro a χ
    rw [← he, ← he, e.weightEquiv_reflection]
  refine ⟨hP, ?_, ?_⟩
  · rw [← roots_image_of_transport t.symm (Iso.refl H) (precomp_square t), ← hQ.2.1]
    ext χ
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨Q.root (e.indexEquiv a), ⟨e.indexEquiv a, rfl⟩, ?_⟩
      rw [← hroot a]
      exact (characterLattice.congr t).symm_apply_apply (P.root a)
    · rintro ⟨_, ⟨a', rfl⟩, rfl⟩
      refine ⟨e.indexEquiv.symm a', ?_⟩
      apply (characterLattice.congr t).injective
      rw [hroot, Equiv.apply_symm_apply]
      exact ((characterLattice.congr t).apply_symm_apply (Q.root a')).symm
  · intro α
    obtain ⟨n, τ, hn, hτ⟩ := hQ.2.2 (e.indexEquiv α)
    refine ⟨_, _, hn.transport t.symm (Iso.refl H) (precomp_square t), ?_⟩
    apply LinearEquiv.ext
    intro χ
    apply (characterLattice.congr t).injective
    rw [hrefl, ← hτ]
    simp only [characterAut_apply, characterLattice.congr_apply, Iso.trans_inv,
      Iso.symm_inv, Iso.symm_symm_eq, Category.assoc, Iso.inv_hom_id_assoc]

omit [IsAffineHom H.X.hom] in
/-- Precomposition with the underlying morphism of a torus isomorphism preserves
maximal tori. -/
theorem IsMaximalTorus.precomp_torusIso (t : T ≅ T') {i : T'.toGrp ⟶ H}
    (hi : IsMaximalTorus i) : IsMaximalTorus (CommGroupScheme.groupHom t.hom ≫ i) :=
  IsMaximalTorus.iso_comp (torusGroupIso t) hi

end Transport

namespace PinnedIsomorphism

/-- The hypotheses of `pinnedIsomorphismStatement_of_prerequisites`: the Isomorphism
Theorem for split groups sharing a maximal torus, scaling of the chosen simple-root
vectors by an automorphism that is the identity on the pinned torus, and rigidity of
pinned automorphisms. -/
def Prerequisites : Prop :=
  SplitCommonTorusIsomorphismStatement.{u} ∧ PinnedRootScalingStatement.{u} ∧
    PinnedAutomorphismRigidityStatement.{u}

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : SplitPinning G) (q : SplitPinning H)

/-- Existence: a pinned isomorphism whose torus component is the torus lift of `e`
and whose index bijection is that of `e`. -/
theorem exists_iso (hC : SplitCommonTorusIsomorphismStatement.{u})
    (hS : PinnedRootScalingStatement.{u}) (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (hsimple : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support) :
    ∃ f : SplitPinning.Iso p q, f.torusIso = p.torusIsoOfRootDatumEquiv q e ∧
      f.indexEquiv = e.indexEquiv := by
  have hR : IsRootDatumOf
      (CommGroupScheme.groupHom (p.torusIsoOfRootDatumEquiv q e).hom ≫ q.inclusion)
      p.rootDatum :=
    IsRootDatumOf.precomp_torusIso _ q.isRootDatum p.isRootDatum.1 e fun χ =>
      (DFunLike.congr_fun (p.torusIsoOfRootDatumEquiv_character q e) χ).symm
  have hM : IsMaximalTorus
      (CommGroupScheme.groupHom (p.torusIsoOfRootDatumEquiv q e).hom ≫ q.inclusion) :=
    IsMaximalTorus.precomp_torusIso _ q.isMaximalTorus
  obtain ⟨ψ, hψ⟩ := hC k G H p.isConnectedReductive q.isConnectedReductive p.torus
    p.isSplitTorus p.inclusion _ p.isMaximalTorus hM p.rootIndex p.rootIndex
    p.rootDatum p.rootDatum p.isRootDatum hR (Equiv.refl _) rfl rfl
  let s : p.base.support → q.base.support := fun a =>
    ⟨e.indexEquiv a, (hsimple a).mp a.property⟩
  have hmem : ∀ a : p.base.support,
      Lie.targetMapLinear ψ.hom (CommRingCat.of k) (p.pinning.rootVector a) ∈
        weightSpace q.inclusion (q.rootDatum.root (s a)) := by
    intro a
    have h := lieKernelHomLinear_mem_weightSpace_of_transport _ ψ.hom hψ _
      (p.pinning.rootVector_mem a)
    rwa [p.torusIsoOfRootDatumEquiv_root q e] at h
  let c : p.base.support → k := fun a =>
    (q.pinning.trivialization (s a)).symm ⟨_, hmem a⟩
  have hc : ∀ a, Lie.targetMapLinear ψ.hom (CommRingCat.of k) (p.pinning.rootVector a) =
      c a • q.pinning.rootVector (s a) := by
    intro a
    rw [← q.pinning.trivialization_apply_val, LinearEquiv.apply_symm_apply]
  have hc0 : ∀ a, c a ≠ 0 := by
    intro a h0
    apply p.pinning.rootVector_ne_zero a
    have h := congrArg (Lie.targetMapLinear ψ.inv (CommRingCat.of k)) (hc a)
    rwa [Lie.targetMapLinear_hom_inv, h0, zero_smul, map_zero] at h
  obtain ⟨σ, hσ, hσX⟩ := hS k G p fun a => (Units.mk0 (c a) (hc0 a))⁻¹
  refine ⟨{ torusIso := p.torusIsoOfRootDatumEquiv q e
            groupIso := σ ≪≫ ψ
            square := ?_
            indexEquiv := e.indexEquiv
            root_eq := p.torusIsoOfRootDatumEquiv_root q e
            coroot_eq := p.torusIsoOfRootDatumEquiv_coroot q e
            simple_iff := hsimple
            rootVector_eq := ?_ }, rfl, rfl⟩
  · rw [Iso.trans_hom, ← Category.assoc, hσ, hψ]
  · intro a
    rw [Iso.trans_hom, Lie.targetMapLinear_comp, LinearMap.comp_apply, hσX, map_smul, hc,
      smul_smul, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ (hc0 a), one_smul]

/-- Uniqueness: under rigidity, a pinned isomorphism is determined by its torus
component and its index bijection. -/
theorem iso_ext (hR : PinnedAutomorphismRigidityStatement.{u}) {f f' : SplitPinning.Iso p q}
    (ht : f.torusIso = f'.torusIso) (hi : f.indexEquiv = f'.indexEquiv) : f = f' := by
  have hg : f.groupIso = f'.groupIso := by
    have hσ := hR k G p (f.groupIso ≪≫ f'.groupIso.symm) ?_ ?_
    · apply Iso.ext
      have h := congrArg Iso.hom hσ
      rw [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom] at h
      exact (Iso.comp_inv_eq_id _).mp h
    · rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, f.square, Category.assoc,
        torusTransport_inverse_square f'.torusIso f'.groupIso f'.square, ← Category.assoc, ht]
      change CommGroupScheme.groupHom (f'.torusIso.hom ≫ f'.torusIso.inv) ≫ p.inclusion =
        p.inclusion
      rw [Iso.hom_inv_id]
      exact Category.id_comp _
    · intro a
      have hs : (⟨f.indexEquiv a, (f.simple_iff a).mp a.property⟩ : q.base.support) =
          ⟨f'.indexEquiv a, (f'.simple_iff a).mp a.property⟩ :=
        Subtype.ext (congrArg (fun g : p.rootIndex ≃ q.rootIndex => g a) hi)
      rw [Iso.trans_hom, Iso.symm_hom, Lie.targetMapLinear_comp, LinearMap.comp_apply,
        f.rootVector_eq, hs, ← f'.rootVector_eq, Lie.targetMapLinear_hom_inv]
  obtain ⟨t, g, sq, ie, r, c, s, v⟩ := f
  obtain ⟨t', g', sq', ie', r', c', s', v'⟩ := f'
  dsimp only at ht hi hg
  subst ht hi hg
  rfl

/-- The pinned Isomorphism Theorem follows from `Prerequisites`. -/
theorem pinnedIsomorphismStatement_of_prerequisites (h : Prerequisites.{u}) :
    PinnedIsomorphismStatement.{u} := by
  intro k _ G H _ _ p q e hsimple
  obtain ⟨f, hft, hfi⟩ := exists_iso p q h.1 h.2.1 e hsimple
  refine ⟨f, ⟨?_, ?_, hfi⟩, ?_⟩
  · rw [hft]
    exact p.torusIsoOfRootDatumEquiv_character q e
  · rw [hft]
    exact p.torusIsoOfRootDatumEquiv_cocharacter q e
  · rintro f' ⟨h1, -, h3⟩
    apply iso_ext p q h.2.2
    · apply p.isSplitTorus.iso_ext_of_character_congr
      ext χ
      rw [hft]
      exact (DFunLike.congr_fun h1 χ).trans
        (DFunLike.congr_fun (p.torusIsoOfRootDatumEquiv_character q e) χ).symm
    · rw [h3, hfi]

end PinnedIsomorphism

end Langlands.GroupScheme
