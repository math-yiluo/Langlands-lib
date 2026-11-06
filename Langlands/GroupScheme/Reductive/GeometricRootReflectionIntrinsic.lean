import Langlands.GroupScheme.Reductive.GeometricRootReflectionConstruction
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Geometric reflections from the chosen actual cocharacter centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G M : GroupScheme S} {T : CommGroupScheme S}
  (i : T.toGrp ⟶ G) (chiT : (Gm S).toGrp ⟶ T.toGrp) {j : M ⟶ G}
  (hj : (centralizer (chiT ≫ i)).IsRepresentedBy j)

/-- The defining cocharacter is central in its actual represented centralizer. -/
theorem isCentral_cocharacter_torusFactor :
    IsCentral (chiT ≫ torusFactor i chiT hj) := by
  intro U x V a y
  change (a ≫ (x ≫ (chiT ≫ torusFactor i chiT hj).hom.hom)) * y =
    y * (a ≫ (x ≫ (chiT ≫ torusFactor i chiT hj).hom.hom))
  apply hj.1.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  have hy : y ≫ j.hom.hom ∈ (centralizer (chiT ≫ i)).carrier V := by
    rw [← hj.2]
    exact ⟨y, rfl⟩
  have hc := (commute_cocharacter_of_mem_centralizer (chiT ≫ i) hy (a ≫ x)).symm.eq
  simpa only [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom,
    torusFactor_comp] using hc

end Dynamic

namespace RankOneCentralizerDetection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
  (hG : IsConnectedReductive G) (hi : IsMaximalTorus i)
  (α : characterLattice T) (hα : α ∈ roots i)

include hG hi

/-- The actual generic cocharacter centralizer has a nonidentity normalizer
class of its factored maximal torus. -/
theorem exists_nonidentityNormalizer :
    Nonempty {n : normalizerPoints (T := T) (torusHom i hT α hα.1) //
      (QuotientGroup.mk n : relativeWeylGroup (T := T) (torusHom i hT α hα.1)) ≠ 1} := by
  let L := groupScheme i hT α hα.1
  let t := torusHom i hT α hα.1
  have hL : IsConnectedReductive L :=
    dynamicCentralizerReductive k G hG _ L (inclusion i hT α hα.1)
      (isClosedSubgroup_inclusion i hT α hα.1) (isRepresentedBy_inclusion i hT α hα.1)
  have hmax : IsMaximalTorus t :=
    IsMaximalTorus.of_comp (isClosedSubgroup_inclusion i hT α hα.1) (by
      rwa [torusHom_comp])
  have hroot : α ∈ roots t :=
    RootReducedness.mem_roots_torusFactor i (cocharacter i hT α hα.1)
      (isRepresentedBy_inclusion i hT α hα.1) hα (pairing_cocharacter i hT α hα.1)
  have : Smooth L.X.hom := hL.smooth
  have : IsAffineHom L.X.hom := hL.isAffineHom
  have : ConnectedSpace L.X.left := hL.connectedSpace
  obtain ⟨B, b, tb, hpair, -, htb⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hL.isPseudoReductive t hT hmax hroot
  have : Smooth B.X.hom := hpair.1.smooth
  have : IsAffineHom B.X.hom := hpair.1.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hpair.1.connectedSpace
  have hconj : MaximalToriAreConjugate B :=
    solvableMaximalTorusConjugacy k B hpair.1.isSolvableGroupScheme
  let D := hpair.1.properQuotientData_of_solvableProperFixedPoint solvableProperFixedPoint
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  exact ⟨nonidentityNormalizerOfRootedSolvableQuotient
    hL.isPseudoReductive t hmax hT hroot b hpair.1.isClosedSubgroup
    hpair.1.isSolvableGroupScheme tb htb hconj D.projection D.fibers⟩

/-- A normalizer in the actual rank-one centralizer inverts the specified
root and fixes the exact defining cocharacter. -/
theorem exists_normalizer_inverting_and_fixing :
    haveI := (isClosedSubgroup_torusHom i hT α hα.1 hi.2.1).mono
    ∃ n : normalizerPoints (T := T) (torusHom i hT α hα.1),
      (normalizingAut (T := T) (torusHom i hT α hα.1) n).hom ≫ α = -α ∧
      cocharacter i hT α hα.1 ≫
        (normalizingAut (T := T) (torusHom i hT α hα.1) n).hom =
          cocharacter i hT α hα.1 := by
  let L := groupScheme i hT α hα.1
  let t := torusHom i hT α hα.1
  let := (isClosedSubgroup_torusHom i hT α hα.1 hi.2.1).mono
  have hL : IsConnectedReductive L :=
    dynamicCentralizerReductive k G hG _ L (inclusion i hT α hα.1)
      (isClosedSubgroup_inclusion i hT α hα.1) (isRepresentedBy_inclusion i hT α hα.1)
  have hmax : IsMaximalTorus t :=
    IsMaximalTorus.of_comp (isClosedSubgroup_inclusion i hT α hα.1) (by
      rwa [torusHom_comp])
  have hroot : α ∈ roots t :=
    RootReducedness.mem_roots_torusFactor i (cocharacter i hT α hα.1)
      (isRepresentedBy_inclusion i hT α hα.1) hα (pairing_cocharacter i hT α hα.1)
  obtain ⟨n⟩ := exists_nonidentityNormalizer i hT hG hi α hα
  have hinv : (normalizingAut (T := T) t n.val).inv ≫ α = -α := by
    rw [← weylAction_apply (T := T)]
    exact hL.weylAction_eq_neg_of_rankOne t hmax hT
      (roots_pairwise_dependent i hT α hα.1) n.val n.property α hroot
  refine ⟨n.val, ?_, ?_⟩
  · calc
      _ = (normalizingAut (T := T) t n.val).hom ≫
          (-((normalizingAut (T := T) t n.val).inv ≫ α)) := by
        rw [hinv, neg_neg]
      _ = -α := by simp
  · exact normalizingAut_comp_of_central t (cocharacter i hT α hα.1)
      (Dynamic.isCentral_cocharacter_torusFactor i _
        (isRepresentedBy_inclusion i hT α hα.1)) n.val

include hT hα

/-- Rank-one negation in the actual centralizer gives ambient root negation. -/
theorem neg_mem_roots : -α ∈ roots i := by
  let L := groupScheme i hT α hα.1
  let t := torusHom i hT α hα.1
  have hL : IsConnectedReductive L :=
    dynamicCentralizerReductive k G hG _ L (inclusion i hT α hα.1)
      (isClosedSubgroup_inclusion i hT α hα.1) (isRepresentedBy_inclusion i hT α hα.1)
  have hmax : IsMaximalTorus t :=
    IsMaximalTorus.of_comp (isClosedSubgroup_inclusion i hT α hα.1) (by
      rwa [torusHom_comp])
  have hroot : α ∈ roots t :=
    RootReducedness.mem_roots_torusFactor i (cocharacter i hT α hα.1)
      (isRepresentedBy_inclusion i hT α hα.1) hα (pairing_cocharacter i hT α hα.1)
  have hneg : -α ∈ roots t :=
    RootReducedness.neg_mem_roots_of_rankOne_algClosed hL hT t hmax
      (roots_pairwise_dependent i hT α hα.1) hroot
  exact (RootReducedness.mem_roots_of_mem_roots_torusFactor i
    (cocharacter i hT α hα.1) (isRepresentedBy_inclusion i hT α hα.1) hneg).1

end RankOneCentralizerDetection

namespace splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance intrinsicReflection_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance intrinsicReflection_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

variable [hi : IsClosedImmersion i.hom.hom.left] (s : Spec (CommRingCat.of r))

include hi

/-- A normalizer in the actual generic centralizer supplies the geometric
reflection record, without a universal field-reflection premise. -/
theorem exists_geometricRootReflectionData_intrinsic
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    Nonempty (GeometricRootReflectionData I G i s m hm) := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  let j := geometricIdentityComponentHom I G i s
  let hT : IsSplitTorus (commGroupScheme (Spec (CommRingCat.of k)) I).toGrp :=
    isSplitTorus_splitTorus I
  let α : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) :=
    exponentCharacter (Spec (CommRingCat.of k)) I m
  let t := RankOneCentralizerDetection.torusHom (T := commGroupScheme _ I) j hT α hm.1
  let z := RankOneCentralizerDetection.inclusion (T := commGroupScheme _ I) j hT α hm.1
  have hmax : IsMaximalTorus (T := commGroupScheme _ I) j :=
    isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hself
  let : Mono t.hom.hom.left :=
    (RankOneCentralizerDetection.isClosedSubgroup_torusHom
      (T := commGroupScheme _ I) j hT α hm.1 hmax.2.1).mono
  obtain ⟨n, hninv, hnfix⟩ :=
    RankOneCentralizerDetection.exists_normalizer_inverting_and_fixing
      (T := commGroupScheme _ I) j hT hs hmax α hm
  refine ⟨{
    automorphism := normalizingCoordinateIso k I t n
    inverts := ?_
    fixesCocharacter := ?_
    point := n.val ≫ z.hom.hom
    transports := ?_ }⟩
  · have h : normalizingCoordinateIso k I t n (characterLatticeEquiv k I α) =
        -characterLatticeEquiv k I α := by
      change characterMap I I (normalizingGroupIso k I t n).hom
        (characterLatticeEquiv k I α) = _
      rw [characterMap_equiv]
      change characterLatticeEquiv k I
        ((normalizingAut (T := commGroupScheme _ I) t n).hom ≫ α) = _
      rw [hninv]
      exact (characterLatticeEquiv k I).map_neg α
    have hc : characterLatticeEquiv k I α = m := by
      dsimp only [α]
      rw [exponentCharacter_eq_characterLatticeEquiv_symm I k m,
        AddEquiv.apply_symm_apply]
    rw [hc] at h
    exact h
  · rw [exponentCocharacter_rootCentralizerVector,
      exponentIso_normalizingCoordinateIso_hom]
    exact congrArg CommGroupScheme.groupHom hnfix
  · have h := (isNormalizingPoint_normalizingAut
        (T := commGroupScheme _ I) t n).isTransporter
    rw [← exponentIso_normalizingCoordinateIso_hom k I t n] at h
    have htz : t ≫ z = j :=
      RankOneCentralizerDetection.torusHom_comp (T := commGroupScheme _ I) j hT α hm.1
    simpa only [Category.assoc, htz] using h.map z

/-- Choose the actual geometric reflection constructed inside the generic
cocharacter centralizer of the specified root. -/
def geometricRootReflectionDataIntrinsic
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    GeometricRootReflectionData I G i s m hm :=
  Classical.choice (exists_geometricRootReflectionData_intrinsic I G i s hs hself m hm)

omit [DecidableEq I] in
/-- The actual geometric exponent-root set is closed under negation, using
only reductivity and self-centralization in this original fibre. -/
theorem neg_mem_geometricExponentRoots_intrinsic
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    -m ∈ geometricExponentRoots I G i s := by
  have hmax := isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hself
  have h := RankOneCentralizerDetection.neg_mem_roots
    (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
    (isSplitTorus_splitTorus I) hs hmax (exponentCharacter _ I m) hm
  change exponentCharacterLinear _ I (-m) ∈ roots _
  rw [map_neg]
  exact h

end splitTorus

end Langlands.GroupScheme
