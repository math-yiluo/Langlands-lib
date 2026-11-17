import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismPredicate
import Langlands.GroupScheme.Reductive.AffinePinnedFppfPinning
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof

/-! # From exact affine pinned automorphisms to local pinning -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- The bijection of the chosen simple support induced by an exact pinned
automorphism's based root label. -/
def IsPinnedAutomorphism.simplePermutation
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) : M.basis.support ≃ M.basis.support :=
  θ.indexEquiv.subtypeEquiv (h.based M)

/-- The coordinate root datum has its standard dot pairing as soon as the
original base has a point. -/
theorem pairing_eq_dot_of_nonempty [Nonempty M.base]
    (m n : M.coordinates → ℤ) :
    M.rootDatum.toLinearMap m n = ∑ j, m j * n j := by
  let x : M.base := Classical.choice inferInstance
  let k := M.base.residueField x
  let : Algebra M.ring k :=
    (Spec.preimage (M.base.fromSpecResidueField x)).hom.toAlgebra
  exact M.fibrewiseRootDatum.pairing k m n

variable {M}

/-- Exact preservation of one original pinning vector persists on every
actual coefficient test after arbitrary scheme pullback. -/
theorem rootVectorPoint_baseChange_of_vector_eq
    (σ : CategoryTheory.Aut M.group) {s t : M.basis.support}
    (hv : Lie.targetMapLinear σ.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      (M.pinning t 1).val)
    {T : Scheme.{u}} (f : T ⟶ M.base) (A : Type u)
    [CommRing A] [Algebra M.ring A]
    (a : Spec (CommRingCat.of A) ⟶ T)
    (ha : algebraBaseMap M.ring A = a ≫ f) :
    M.rootVectorPoint f A a ha s ≫
        ((baseChange f).map σ.hom).hom.hom.left =
      M.rootVectorPoint f A a ha t := by
  have hmap : ((baseChange f).map σ.hom).hom.hom.left ≫
      pullback.fst M.group.X.hom f =
    pullback.fst M.group.X.hom f ≫ σ.hom.hom.hom.left := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  have hvA := (lieKernelTargetLinear_map σ.hom
    (Algebra.ofId M.ring A) (M.pinning s 1).val).trans
      (congrArg (lieKernelMapLinear M.group (Algebra.ofId M.ring A)) hv)
  have hp := congrArg (fun z => z.toMul.val.left) hvA
  change (M.rootVectorAt A s).val.left ≫ σ.hom.hom.hom.left =
    (M.rootVectorAt A t).val.left at hp
  apply pullback.hom_ext
  · rw [Category.assoc, hmap, ← Category.assoc,
      rootVectorPoint_fst, rootVectorPoint_fst]
    exact hp
  · have hw := Over.w ((baseChange f).map σ.hom).hom.hom
    change ((baseChange f).map σ.hom).hom.hom.left ≫
      pullback.snd M.group.X.hom f = pullback.snd M.group.X.hom f at hw
    rw [Category.assoc, hw]
    exact (M.rootVectorPoint_snd f A a ha s).trans
      (M.rootVectorPoint_snd f A a ha t).symm

/-- An original simple-vector permutation gives the local pinning predicate
on all pullbacks, even when their common scheme is disconnected. -/
theorem preservesLocalPinning_baseChange_of_vector_permutation
    (σ : CategoryTheory.Aut M.group)
    (p : M.basis.support ≃ M.basis.support)
    (hp : ∀ s, Lie.targetMapLinear σ.hom (CommRingCat.of M.ring)
      (M.pinning s 1).val = (M.pinning (p s) 1).val)
    {T : Scheme.{u}} (f : T ⟶ M.base) :
    PreservesLocalPinning ((baseChange f).mapIso σ) := by
  intro A _ _ α β a ha hb
  have hαβ : α = β := by
    apply Algebra.algebra_ext
    intro r
    have hm := congrArg
      (fun z : Spec (CommRingCat.of A) ⟶ M.base => (Spec.preimage z).hom r)
      (ha.trans hb.symm)
    simp only [algebraBaseMap, Spec.preimage_map] at hm
    change α.algebraMap r = β.algebraMap r at hm
    exact hm
  cases hαβ
  exact ⟨p, fun s => rootVectorPoint_baseChange_of_vector_eq σ (hp s) f A a ha⟩

variable (M)

/-- Every exact affine pinned automorphism preserves the concrete local
pinning on every actual pullback. -/
theorem IsPinnedAutomorphism.preservesLocalPinning_baseChange
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) {T : Scheme.{u}} (f : T ⟶ M.base) :
    PreservesLocalPinning ((baseChange f).mapIso σ) := by
  let p := h.simplePermutation M
  obtain ⟨hθ, _, hX⟩ := h
  exact preservesLocalPinning_baseChange_of_vector_permutation σ p hX f

/-- The exact target predicate supplies based coordinate data, with the inverse
label because coordinate characters act contravariantly. -/
theorem IsPinnedAutomorphism.exists_basedCoordinateIso [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) :
    ∃ d : BasedCoordinateIso M.inclusion M.inclusion
      M.rootDatum M.rootDatum M.basis M.basis, d.groupIso = σ := by
  obtain ⟨hθ, ⟨τ, hτ, hχ⟩, _⟩ := h
  refine ⟨{
    groupIso := σ
    torusIso := τ
    rootEquiv := θ⁻¹
    sourcePairing := M.pairing_eq_dot_of_nonempty
    targetPairing := M.pairing_eq_dot_of_nonempty
    simple_iff := M.basedAutomorphisms.inv_mem hθ
    square := hτ
    characters := ?_
  }, rfl⟩
  intro U x m
  change (∏ j, splitTorus.pointsEquiv M.coordinates U (x ≫ τ.hom.hom.hom) j ^ m j) =
    ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ θ.weightEquiv.symm m j
  have hm := hχ U x (θ.weightEquiv.symm m)
  simpa only [RootPairing.Equiv.weightMap_weightEquiv_symm] using hm

/-- Exact affine pinning implies preservation of the canonical cocharacter
after every actual scheme pullback. -/
theorem IsPinnedAutomorphism.preservesCocharacter_baseChange [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) {T : Scheme.{u}} (f : T ⟶ M.base) :
    PreservesCocharacter ((baseChange f).mapIso σ) := by
  obtain ⟨d, hd⟩ := h.exists_basedCoordinateIso M
  have hc := d.cocharacter_comp
  rw [hd] at hc
  change M.cocharacterOver f ≫ (baseChange f).map σ.hom = M.cocharacterOver f
  rw [M.cocharacterOver_eq_baseChange]
  rw [← Dynamic.baseChangeCocharacter_comp_hom, hc]

/-- Exact affine pinning implies preservation of the torus on every actual
scheme pullback. -/
theorem IsPinnedAutomorphism.preservesTorus_baseChange
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) {T : Scheme.{u}} (f : T ⟶ M.base) :
    PreservesTorus ((baseChange f).mapIso σ) := by
  obtain ⟨_, ⟨τ, hτ, _⟩, _⟩ := h
  refine ⟨(splitTorus.baseChangeIso f M.coordinates).symm ≪≫
    (baseChange f).mapIso τ ≪≫ splitTorus.baseChangeIso f M.coordinates, ?_⟩
  simp only [inclusionOver, BasedBorelTransport.baseChangeInclusion,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  simpa only [Functor.map_comp] using
    congrArg (fun a => (splitTorus.baseChangeIso f M.coordinates).inv ≫
      (baseChange f).map a) hτ

/-- Every exact pinned automorphism is concretely pinned on every pullback. -/
theorem IsPinnedAutomorphism.locallyPinned_baseChange [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) {T : Scheme.{u}} (f : T ⟶ M.base) :
    IsLocallyPinned ((baseChange f).mapIso σ) :=
  ⟨h.preservesTorus_baseChange M f, h.preservesCocharacter_baseChange M f,
    h.preservesLocalPinning_baseChange M f⟩

/-- In particular the exact target predicate supplies the fppf-local predicate
used in the relative pinned normalization and uniqueness interfaces. -/
theorem IsPinnedAutomorphism.fppfLocallyPinned_baseChange [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) {T : Scheme.{u}} (f : T ⟶ M.base) :
    IsFppfLocallyPinned ((baseChange f).mapIso σ) :=
  (h.locallyPinned_baseChange M f).fppfLocallyPinned

end Langlands.GroupScheme.AffinePinnedModel
