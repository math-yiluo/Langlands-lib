import Langlands.GroupScheme.Reductive.SplitWeylRationalityStatement
import Langlands.GroupScheme.Reductive.GeometricRootReflectionIntrinsic
import Langlands.GroupScheme.Reductive.RootTorusGeneration
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Rational.RootKernelReflection
import Langlands.GroupScheme.Rational.RankOneCocharacterSymmetrization
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Integral reflections of a split maximal torus from Weyl-group rationality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace RankOneCentralizerDetection

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **The rank-one centralizer centralizes the full root kernel.** For a split maximal torus
of a connected reductive group and a root `α`, the dynamic centralizer of the generic
cocharacter annihilating `α` centralizes the full scheme-theoretic kernel of `α`, on every
test scheme. -/
theorem kernelCentralizer_torusHom_eq_top (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    {α : characterLattice T}
    (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    haveI := hG.isAffineHom
    haveI := hG.smooth
    RelativeRoot.kernelCentralizer (torusHom i hT α hα.1) α = ⊤ := by
  have := hG.isAffineHom
  have := hG.smooth
  have hL : IsConnectedReductive (groupScheme i hT α hα.1) :=
    dynamicCentralizerReductive k G hG _ _ (inclusion i hT α hα.1)
      (isClosedSubgroup_inclusion i hT α hα.1) (isRepresentedBy_inclusion i hT α hα.1)
  have hmax : IsMaximalTorus (torusHom i hT α hα.1) :=
    IsMaximalTorus.of_comp (isClosedSubgroup_inclusion i hT α hα.1) (by
      rwa [torusHom_comp])
  have hroot : α ∈ roots (torusHom i hT α hα.1) :=
    RootReducedness.mem_roots_torusFactor i (cocharacter i hT α hα.1)
      (isRepresentedBy_inclusion i hT α hα.1) hα (pairing_cocharacter i hT α hα.1)
  have : ConnectedSpace (groupScheme i hT α hα.1).X.left := hL.connectedSpace
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  obtain ⟨C, j, hj, hjc, -, -⟩ :=
    RelativeRoot.kernelCentralizerStructure k (groupScheme i hT α hα.1) inferInstance inferInstance T hT
      (torusHom i hT α hα.1) α hα.1
  have hzero := RelativeRoot.weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing
    (torusHom i hT α hα.1)
    (maximalTorusCentralizer k _ hL T (torusHom i hT α hα.1) hmax)
  rw [← hj.2]
  apply range_eq_top_of_torus_and_rootSubgroups (torusHom i hT α hα.1) hT hzero j hjc
  · rw [hj.2]
    exact RelativeRoot.range_le_kernelCentralizer _ α
  · intro β hβ
    rw [hj.2]
    have hdep := roots_pairwise_dependent i hT α hα.1 β hβ α hroot
    rcases rootReducedness k _ hL T hT _ hmax β hβ α hroot hdep with h | h
    · rw [h]
      exact RelativeRoot.subgroup_le_kernelCentralizer _ α
    · rw [h]
      exact RelativeRoot.opposite_subgroup_le_kernelCentralizer _ α

end RankOneCentralizerDetection

namespace SplitWeylRationality

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, a root of a split maximal torus of a connected
reductive group gives a normalizing point whose Weyl class is nontrivial. This is the
construction of the published `RootReducedness.neg_mem_roots_of_rankOne_algClosed`. -/
theorem exists_nonidentityNormalizer_of_algClosed [IsAlgClosed k]
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) {α : characterLattice T}
    (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨B, b, t, hpair, -, ht⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hG.isPseudoReductive i hT hi hα
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
  let n := nonidentityNormalizerOfRootedSolvableQuotient
    hG.isPseudoReductive i hi hT hα b hpair.1.isClosedSubgroup
    hpair.1.isSolvableGroupScheme t ht hconj D.projection D.fibers
  exact ⟨n.val, n.property⟩

/-- Over an arbitrary field, Weyl-group rationality descends a nontrivial Weyl class from an
algebraic closure: a root of a split maximal torus of a connected reductive group gives a
rational normalizing point whose Weyl class is nontrivial. -/
theorem exists_nonidentityNormalizer (hW : SplitMaximalTorusWeylRationalityStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) {α : characterLattice T}
    (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1 := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.2.1.mono
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let ic : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map i
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have hic : IsMaximalTorus ic :=
    (maximalTorusBaseChange k (AlgebraicClosure k) G T i hi.1 hi.2.1).mp hi
  have hαc := (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT i α).mpr hα
  obtain ⟨w, hw⟩ := exists_nonidentityNormalizer_of_algClosed hGc (hT.baseChange b) ic hic hαc
  obtain ⟨n, σ, hn, hσ⟩ := hW k (AlgebraicClosure k) G hG T hT i hi w.val
    (normalizingAut ic w) (isNormalizingPoint_normalizingAut ic w)
  refine ⟨⟨n, σ, hn⟩, fun h1 => hw ?_⟩
  rw [QuotientGroup.eq_one_iff] at h1 ⊢
  have hrefl : σ = Iso.refl T := IsNormalizingPoint.unique i hn (Subgroup.mem_subgroupOf.mp h1)
  have hw' := isNormalizingPoint_normalizingAut ic w
  rw [← hσ, hrefl, Functor.mapIso_refl] at hw'
  exact Subgroup.mem_subgroupOf.mpr hw'

/-- **Integral reflections from Weyl-group rationality.** For a split maximal torus of a
connected reductive group and a root `α`, Weyl-group rationality gives a rational normalizing
point and a cocharacter `ν` with `⟨α, ν⟩ = 2` acting on characters by `χ ↦ χ - ⟨χ, ν⟩ α`. -/
theorem exists_reflection (hW : SplitMaximalTorusWeylRationalityStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) {α : characterLattice T}
    (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    haveI := hi.2.1.mono
    ∃ (n : normalizerPoints i) (ν : cocharacterLattice T),
      latticePairing T α ν = 2 ∧ ∀ χ : characterLattice T,
        weylAction i n χ = χ - latticePairing T χ ν • α := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.2.1.mono
  open RankOneCentralizerDetection in
  have hL : IsConnectedReductive (groupScheme i hT α hα.1) :=
    dynamicCentralizerReductive k G hG _ _ (inclusion i hT α hα.1)
      (isClosedSubgroup_inclusion i hT α hα.1) (isRepresentedBy_inclusion i hT α hα.1)
  open RankOneCentralizerDetection in
  have hmax : IsMaximalTorus (torusHom i hT α hα.1) :=
    IsMaximalTorus.of_comp (isClosedSubgroup_inclusion i hT α hα.1) (by
      rwa [torusHom_comp])
  open RankOneCentralizerDetection in
  have hroot : α ∈ roots (torusHom i hT α hα.1) :=
    RootReducedness.mem_roots_torusFactor i (cocharacter i hT α hα.1)
      (isRepresentedBy_inclusion i hT α hα.1) hα (pairing_cocharacter i hT α hα.1)
  have := hmax.2.1.mono
  obtain ⟨m, hm⟩ := exists_nonidentityNormalizer hW hL hT _ hmax hroot
  have hflip := hL.weylAction_eq_neg_of_rankOne _ hmax hT
    (RankOneCentralizerDetection.roots_pairwise_dependent i hT α hα.1) m hm α hroot
  have hc : m.val ∈ (RelativeRoot.kernelCentralizer
      (RankOneCentralizerDetection.torusHom i hT α hα.1) α).carrier (Over.mk (𝟙 _)) := by
    rw [RankOneCentralizerDetection.kernelCentralizer_torusHom_eq_top hG hT i hi hα]
    trivial
  obtain ⟨ν, ⟨h2, href⟩, -⟩ := hT.existsUnique_coroot_of_mem_kernelCentralizer _ α hα.1 m hflip hc
  refine ⟨normalizerPointsMap _ (RankOneCentralizerDetection.inclusion i hT α hα.1) i
    (RankOneCentralizerDetection.torusHom_comp i hT α hα.1) m, ν, h2, fun χ => ?_⟩
  rw [weylAction_normalizerPointsMap]
  exact href χ

/-- **Integral reflection data from Weyl-group rationality.** For a split maximal torus of a
connected reductive group, Weyl-group rationality provides, for every actual root, a rational
normalizing point and an integral coroot pairing to two with the root, acting on characters by
the reflection formula. The choices are those of `exists_reflection`. -/
def reflectionData (hW : SplitMaximalTorusWeylRationalityStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.2.1.mono
    RelativeRootReflectionData i :=
  haveI := hG.isAffineHom
  haveI := hi.2.1.mono
  { coroot := fun α =>
      Classical.choose (Classical.choose_spec (exists_reflection hW hG hT i hi α.property))
    representative := fun α => Classical.choose (exists_reflection hW hG hT i hi α.property)
    pair_self := fun α =>
      (Classical.choose_spec (Classical.choose_spec
        (exists_reflection hW hG hT i hi α.property))).1
    action := fun α =>
      (Classical.choose_spec (Classical.choose_spec
        (exists_reflection hW hG hT i hi α.property))).2 }

end SplitWeylRationality

end Langlands.GroupScheme
