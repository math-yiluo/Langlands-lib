import Langlands.GroupScheme.Reductive.IsogenyRootFunctorComparison
import Langlands.GroupScheme.FiniteHomDimension
import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.GroupScheme.SubgroupFunctor.FppfProductImage

/-! # Actual restrictions of split isogenies to root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

section Representatives

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    [P.IsReduced]

/-- Reduced actual root data exclude all higher positive root multiples. -/
theorem hasNoHigherRoots_of_isRootDatumOf
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hP : IsRootDatumOf i P) (j : J) : HasNoHigherRoots i (P.root j) := by
  let : HasUniqueDiv (ℚ ⊗[ℤ] characterLattice T) := HasUniqueDiv.of_module_rat _
  let : HasUniqueDiv (characterLattice T) :=
    hT.character_toRat_injective.hasUniqueDiv Langlands.LinearAlgebra.RationalSpan.toRat
  intro n hn
  let : n.AtLeastTwo := ⟨hn⟩
  rw [relativeRoots_eq_roots, ← hP.2.1]
  exact P.nsmul_notMem_range_root

variable [Smooth G.X.hom]

/-- Every supplied representative of a nonzero intrinsic root is closed. -/
theorem closed_of_isRepresentedBy_subgroup
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0)
    {U : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G}
    (hjU : (subgroup i a).IsRepresentedBy jU) : IsClosedSubgroup jU := by
  obtain ⟨V, jV, hjV, hc, _, _⟩ :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hT i a ha
  let : IsClosedImmersion jV.hom.hom.left := hc
  have he := hjU.isoOfIsRepresentedBy_hom_comp hjV
  have he' := congrArg (fun f => f.hom.hom.left) he
  change IsClosedImmersion jU.hom.hom.left
  rw [← he']
  change IsClosedImmersion ((hjU.isoOfIsRepresentedBy hjV).hom.hom.hom.left ≫
    jV.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

/-- Every supplied representative of a nonzero intrinsic root is connected. -/
theorem connectedSpace_of_isRepresentedBy_subgroup
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0)
    {U : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G}
    (hjU : (subgroup i a).IsRepresentedBy jU) : ConnectedSpace U.X.left := by
  obtain ⟨V, jV, hjV, _, _, hconn⟩ :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hT i a ha
  let : ConnectedSpace V.X.left := hconn
  exact DynamicConnected.connectedSpace_of_iso (hjU.isoOfIsRepresentedBy hjV)

/-- The actual Lie kernel of every supplied split-root representative is a line. -/
theorem finrank_lieKernel_eq_one_of_isRepresentedBy_root
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hP : IsRootDatumOf i P) (j : J)
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom] {jU : U ⟶ G}
    (hjU : (subgroup i (P.root j)).IsRepresentedBy jU) :
    Module.finrank k (Additive (lieKernel U k)) = 1 := by
  let : IsAffineHom U.X.hom :=
    (closed_of_isRepresentedBy_subgroup hT i (P.ne_zero j) hjU).isAffineHom
  have hroot : P.root j ∈ roots i := hP.2.1 ▸ Set.mem_range_self j
  obtain ⟨e⟩ := splitRootLieLine k G hG T hT i hi (P.root j) hroot
  have er := representedRootLieEquiv hT i (P.ne_zero j)
    (hasNoHigherRoots_of_isRootDatumOf P hT i hP j) hjU
  rw [er.finrank_eq, ← e.finrank_eq, Module.finrank_self]

end Representatives

section Restriction

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] [Smooth G'.X.hom]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [P.IsReduced] [P'.IsReduced]
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G')
    (hP' : IsRootDatumOf i' P')
    (φ : G ⟶ G') (t : T ⟶ T')
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    {p : ℕ} (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hweight : ∀ χ, f.weightMap χ = t ≫ χ) (j' : J')

/-- The actual homomorphism induced between arbitrary corresponding root
representatives by the compatible ambient homomorphism. -/
def rootRestrictionOfRootDatumIsogeny
    {U U' : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G} {jU' : U' ⟶ G'}
    (hjU : (subgroup i (P.root (f.indexEquiv j'))).IsRepresentedBy jU)
    (hjU' : (subgroup i' (P'.root j')).IsRepresentedBy jU') : U ⟶ U' :=
  hjU.restrictionHom hjU' φ (fun _ _ hg =>
    comp_mem_subgroup_of_rootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f hweight j' hg)

omit [IsAffineHom G.X.hom] in
/-- The root restriction commutes with the actual representative inclusions. -/
theorem rootRestrictionOfRootDatumIsogeny_comp
    {U U' : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G} {jU' : U' ⟶ G'}
    (hjU : (subgroup i (P.root (f.indexEquiv j'))).IsRepresentedBy jU)
    (hjU' : (subgroup i' (P'.root j')).IsRepresentedBy jU') :
    rootRestrictionOfRootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f hweight j'
      hjU hjU' ≫ jU' = jU ≫ φ :=
  hjU.restrictionHom_comp hjU' φ _

/-- A finite ambient map restricts to an actual isogeny on corresponding
split roots. No separability or smoothness of its kernel is needed. -/
theorem isIsogeny_rootRestrictionOfRootDatumIsogeny
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (hP : IsRootDatumOf i P)
    [IsFinite φ.hom.hom.left]
    {U U' : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G} {jU' : U' ⟶ G'}
    (hjU : (subgroup i (P.root (f.indexEquiv j'))).IsRepresentedBy jU)
    (hjU' : (subgroup i' (P'.root j')).IsRepresentedBy jU') :
    IsIsogeny (rootRestrictionOfRootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f
      hweight j' hjU hjU') := by
  let : Smooth G.X.hom := hG.smooth
  let hc := closed_of_isRepresentedBy_subgroup hT i (P.ne_zero _) hjU
  let hc' := closed_of_isRepresentedBy_subgroup hT' i' (P'.ne_zero _) hjU'
  let : IsClosedImmersion jU.hom.hom.left := hc
  let : IsClosedImmersion jU'.hom.hom.left := hc'
  let : IsAffineHom U.X.hom := hc.isAffineHom
  let : IsAffineHom U'.X.hom := hc'.isAffineHom
  let : Smooth U.X.hom := smooth_of_isRepresentedBy_subgroup hT i _ (P.ne_zero _) hjU
  let : Smooth U'.X.hom := smooth_of_isRepresentedBy_subgroup hT' i' _ (P'.ne_zero _) hjU'
  let : ConnectedSpace U.X.left :=
    connectedSpace_of_isRepresentedBy_subgroup hT i (P.ne_zero _) hjU
  let : ConnectedSpace U'.X.left :=
    connectedSpace_of_isRepresentedBy_subgroup hT' i' (P'.ne_zero _) hjU'
  let q := rootRestrictionOfRootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f
    hweight j' hjU hjU'
  have hq : q ≫ jU' = jU ≫ φ :=
    rootRestrictionOfRootDatumIsogeny_comp P P' hT hT' i i' hP' φ t hsquare f
      hweight j' hjU hjU'
  have hq' : q.hom.hom.left ≫ jU'.hom.hom.left =
      jU.hom.hom.left ≫ φ.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hq
  have : IsFinite (q.hom.hom.left ≫ jU'.hom.hom.left) := by
    rw [hq']
    infer_instance
  let : IsFinite q.hom.hom.left := IsFinite.of_comp _ jU'.hom.hom.left
  apply isIsogeny_of_isFinite_of_finrank_eq q
  rw [finrank_lieKernel_eq_one_of_isRepresentedBy_root P hG hT i hi hP _ hjU,
    finrank_lieKernel_eq_one_of_isRepresentedBy_root P' hG' hT' i' hi' hP' _ hjU']

include hT hT' hP' t hsquare hweight

/-- Corresponding intrinsic root subgroups have the actual fppf-image relation. -/
theorem isFppfImage_of_rootDatumIsogeny
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (hP : IsRootDatumOf i P)
    [IsFinite φ.hom.hom.left] :
    SubgroupFunctor.IsFppfImage (subgroup i (P.root (f.indexEquiv j')))
      (subgroup i' (P'.root j')) φ := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨U, jU, hjU, hc, hsm, hconn⟩ :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hT i (P.root _) (P.ne_zero _)
  obtain ⟨U', jU', hjU', hc', hsm', hconn'⟩ :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hT' i' (P'.root j') (P'.ne_zero _)
  let : Smooth U'.X.hom := hsm'
  let : IsLocallyNoetherian U'.X.left := LocallyOfFiniteType.isLocallyNoetherian U'.X.hom
  let q := rootRestrictionOfRootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f
    hweight j' hjU hjU'
  have hq : IsIsogeny q := isIsogeny_rootRestrictionOfRootDatumIsogeny
    P P' hT hT' i i' hP' φ t hsquare f hweight j' hG hG' hi hi' hP hjU hjU'
  let : IsFinite q.hom.hom.left := hq.1
  exact ⟨U, U', jU, jU', q, hjU, hjU',
    (rootRestrictionOfRootDatumIsogeny_comp P P' hT hT' i i' hP' φ t hsquare f
      hweight j' hjU hjU').symm, hq.2.1, hq.2.2, inferInstance⟩

/-- The whole-root fppf-image correspondence is exactly the supplied root-index
correspondence. -/
theorem isFppfImage_iff_index_eq
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (hP : IsRootDatumOf i P)
    [IsFinite φ.hom.hom.left] (j : J) :
    SubgroupFunctor.IsFppfImage (subgroup i (P.root j))
      (subgroup i' (P'.root j')) φ ↔ j = f.indexEquiv j' := by
  constructor
  · intro himage
    let l := f.indexEquiv.symm j
    have hj : f.indexEquiv l = j := f.indexEquiv.apply_symm_apply j
    have hmap : (subgroup i (P.root j)).map φ ≤ subgroup i' (P'.root l) := by
      rintro Z x ⟨y, hy, rfl⟩
      rw [← hj] at hy
      exact comp_mem_subgroup_of_rootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f
        hweight l hy
    have hloc : (subgroup i' (P'.root l)).IsFppfLocal := by
      obtain ⟨V, jV, hjV, _⟩ :=
        subgroup_isSmoothConnectedClosed_of_ne_zero hT' i' (P'.root l) (P'.ne_zero l)
      let : Mono jV.hom.hom := hjV.1
      rw [← hjV.2]
      exact SubgroupFunctor.isFppfLocal_range jV
    have hle := himage.le_of_map_le hloc hmap
    have he : j' = l :=
      (subgroup_le_subgroup_iff_of_isRootDatumOf P' hT' i' hP' j' l).mp hle
    rw [he, hj]
  · rintro rfl
    exact isFppfImage_of_rootDatumIsogeny P P' hT hT' i i' hP' φ t hsquare f hweight j'
      hG hG' hi hi' hP

end Restriction

end Langlands.GroupScheme.RelativeRoot
