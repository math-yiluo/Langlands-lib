import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Coroot inheritance for the same actual torus in a subgroup -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) {J : Type v} {K : Type w}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {R : RootDatum K (characterLattice T) (cocharacterLattice T)}

section CorootUniqueness

variable [Mono i.hom.hom.left] [Finite (weylImage i)]

/-- An actual normalizer reflection determines the coroot of a supplied
actual root datum when the full ambient Weyl image is finite. -/
theorem IsRootDatumOf.coroot_eq_of_weylAction_of_finite_weylImage
    (hP : IsRootDatumOf i P) (p : J) (ν : cocharacterLattice T)
    (hν : latticePairing T (P.root p) ν = 2) (n : normalizerPoints i)
    (hn : ∀ χ, weylAction i n χ = χ - latticePairing T χ ν • P.root p) :
    ν = P.coroot p := by
  obtain ⟨m, τ, hm, hτ⟩ := hP.2.2 p
  let m' : normalizerPoints i := ⟨m, τ, hm⟩
  have ht : weylAction i m' = P.reflection p := by
    ext χ
    rw [weylAction_eq i (n := m') (σ := τ) hm χ]
    change characterAut τ χ = _
    rw [hτ]
  let a : weylImage i := ⟨weylAction i n, n, rfl⟩
  let b : weylImage i := ⟨weylAction i m', m', rfl⟩
  have horder : IsOfFinOrder (weylAction i n * P.reflection p) := by
    have hfin := (weylImage i).subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
    change IsOfFinOrder (weylAction i n * weylAction i m') at hfin
    rwa [ht] at hfin
  let f := (latticePairing T).flip ν
  let g := (latticePairing T).flip (P.coroot p)
  have hg : g (P.root p) = 2 := by
    change latticePairing T (P.root p) (P.coroot p) = 2
    rw [← hP.1]
    exact P.root_coroot_two p
  have heq := Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections
    (P.root p) f g (weylAction i n) (P.reflection p) hν hg hn
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - P.toLinearMap χ (P.coroot p) • P.root p = _
      rw [hP.1]
      rfl) horder
  apply P.flip.toPerfPair.injective
  ext χ
  change P.toLinearMap χ ν = P.toLinearMap χ (P.coroot p)
  rw [hP.1]
  exact LinearMap.congr_fun heq χ

/-- A point normalizing the torus through the explicit lattice reflection
forces its defining cocharacter to be the actual coroot. -/
theorem IsRootDatumOf.coroot_eq_of_normalizing_latticeReflectionIso
    (hP : IsRootDatumOf i P) (p : J) {α : characterLattice T}
    (hroot : P.root p = α) (ν : cocharacterLattice T)
    (hν : latticePairing T α ν = 2)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : IsNormalizingPoint i n (latticeReflectionIso α ν hν)) :
    ν = P.coroot p := by
  subst α
  let n' : normalizerPoints i := ⟨n, latticeReflectionIso (P.root p) ν hν, hn⟩
  apply hP.coroot_eq_of_weylAction_of_finite_weylImage i p ν hν n'
  intro χ
  rw [weylAction_eq i (n := n') hn χ]
  exact characterAut_latticeReflectionIso (P.root p) ν hν χ

/-- Equal roots have equal coroots for supplied actual root data of the same
torus in a subgroup and its ambient group. -/
theorem IsRootDatumOf.coroot_eq_of_comp_of_finite_weylImage
    (hP : IsRootDatumOf i P) (iH : T.toGrp ⟶ H) (j : H ⟶ G)
    (hij : iH ≫ j = i) (hR : IsRootDatumOf iH R)
    {p : J} {r : K} (hroot : P.root p = R.root r) :
    P.coroot p = R.coroot r := by
  obtain ⟨n, σ, hn, hσ⟩ := hR.2.2 r
  have hn' : IsNormalizingPoint i (n ≫ j.hom.hom) σ := hij ▸ hn.comp j
  let n' : normalizerPoints i := ⟨n ≫ j.hom.hom, σ, hn'⟩
  have hν : latticePairing T (P.root p) (R.coroot r) = 2 := by
    rw [hroot, ← hR.1]
    exact R.root_coroot_two r
  symm
  apply hP.coroot_eq_of_weylAction_of_finite_weylImage i p (R.coroot r) hν n'
  intro χ
  rw [weylAction_eq i (n := n') (σ := σ) hn' χ]
  change characterAut σ χ = _
  rw [hσ, RootPairing.reflection_apply]
  change χ - R.toLinearMap χ (R.coroot r) • R.root r = _
  rw [hR.1, ← hroot]

end CorootUniqueness

/-- An integral root and coroot comparison on unchanged character and
cocharacter lattices, retaining an actual embedding of root indices. -/
structure SameTorusRootDatumEmbedding
    {J K X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (R : RootDatum K X Y) where
  index : K ↪ J
  root_eq : ∀ r, P.root (index r) = R.root r
  coroot_eq : ∀ r, P.coroot (index r) = R.coroot r

/-- The root-support inclusion embeds the subgroup root indices into the
ambient root indices, without using coroots. -/
def IsRootDatumOf.subgroupRootIndexEmbedding
    (hP : IsRootDatumOf i P) (iH : T.toGrp ⟶ H) (hR : IsRootDatumOf iH R)
    (hroots : roots iH ⊆ roots i) : K ↪ J where
  toFun r := (Equiv.ofInjective P.root P.root.injective).symm
    ⟨R.root r, by
      rw [hP.2.1]
      apply hroots
      rw [← hR.2.1]
      exact ⟨r, rfl⟩⟩
  inj' r r' h := R.root.injective (congrArg Subtype.val
    ((Equiv.ofInjective P.root P.root.injective).symm.injective h))

@[simp]
theorem IsRootDatumOf.subgroupRootIndexEmbedding_root
    (hP : IsRootDatumOf i P) (iH : T.toGrp ⟶ H) (hR : IsRootDatumOf iH R)
    (hroots : roots iH ⊆ roots i) (r : K) :
    P.root (hP.subgroupRootIndexEmbedding i iH hR hroots r) = R.root r := by
  change P.root ((Equiv.ofInjective P.root P.root.injective).symm _) = _
  exact congrArg Subtype.val
    ((Equiv.ofInjective P.root P.root.injective).apply_symm_apply _)

/-- Construct the integral root/coroot embedding for a supplied actual subgroup
root datum whose root support is contained in the ambient support. -/
def IsRootDatumOf.sameTorusSubgroupEmbedding
    [Mono i.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (iH : T.toGrp ⟶ H) (j : H ⟶ G)
    (hij : iH ≫ j = i) (hR : IsRootDatumOf iH R)
    (hroots : roots iH ⊆ roots i) : SameTorusRootDatumEmbedding P R where
  index := hP.subgroupRootIndexEmbedding i iH hR hroots
  root_eq := hP.subgroupRootIndexEmbedding_root i iH hR hroots
  coroot_eq r := hP.coroot_eq_of_comp_of_finite_weylImage i iH j hij hR
    (hP.subgroupRootIndexEmbedding_root i iH hR hroots r)

namespace SameTorusRootDatumEmbedding

variable {J K X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootDatum J X Y} {R : RootDatum K X Y}
    (e : SameTorusRootDatumEmbedding P R)

/-- The subgroup coroot range is the image of its index embedding under the
ambient coroot embedding. -/
theorem range_coroot : Set.range R.coroot = P.coroot '' Set.range e.index := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨e.index r, ⟨r, rfl⟩, e.coroot_eq r⟩
  · rintro ⟨p, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (e.coroot_eq r).symm⟩

/-- Root-support equality identifies the range of the root-index embedding. -/
theorem range_index_eq (s : Set J) (hs : Set.range R.root = P.root '' s) :
    Set.range e.index = s := by
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    have hr : R.root r ∈ P.root '' s := hs ▸ Set.mem_range_self r
    obtain ⟨p, hp, heq⟩ := hr
    have heq' : p = e.index r := P.root.injective (heq.trans (e.root_eq r).symm)
    rwa [heq'] at hp
  · intro hp
    have hmem : P.root p ∈ Set.range R.root := hs.symm ▸ ⟨p, hp, rfl⟩
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, P.root.injective ((e.root_eq r).trans hr)⟩

include e in
/-- A root-support identification gives the corresponding integral coroot-span
identification, on the actual unchanged cocharacter lattice. -/
theorem corootSpan_eq (s : Set J) (hs : Set.range R.root = P.root '' s) :
    R.corootSpan ℤ = Submodule.span ℤ (P.coroot '' s) := by
  change Submodule.span ℤ (Set.range R.coroot) = _
  rw [e.range_coroot, e.range_index_eq s hs]

end SameTorusRootDatumEmbedding

end Langlands.GroupScheme
