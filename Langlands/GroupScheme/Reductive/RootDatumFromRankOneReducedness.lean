import Langlands.GroupScheme.Reductive.SplitRootReflectionReduction
import Langlands.GroupScheme.Reductive.SplitWeylRationality
import Langlands.GroupScheme.Reductive.RootDatumFiniteWeylAssembly

/-! # Split root data from rank-one reducedness -/

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
test scheme, assuming rank-one reducedness. -/
theorem kernelCentralizer_torusHom_eq_top_of_rankOneReducedness
    (hrank : RankOneRootReducednessStatement.{u}) (hG : IsConnectedReductive G)
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
    rcases hrank k _ hL T hT _ hmax (roots_pairwise_dependent i hT α hα.1)
      β hβ α hroot with h | h
    · rw [h]
      exact RelativeRoot.subgroup_le_kernelCentralizer _ α
    · rw [h]
      exact RelativeRoot.opposite_subgroup_le_kernelCentralizer _ α

end RankOneCentralizerDetection

namespace SplitWeylRationality

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Integral reflections from rank-one reducedness and Weyl-group rationality.** For a
split maximal torus of a connected reductive group and a root `α`, the two hypotheses give a
rational normalizing point and a cocharacter `ν` with `⟨α, ν⟩ = 2` acting on characters by
`χ ↦ χ - ⟨χ, ν⟩ α`. -/
theorem exists_reflection_of_rankOneReducedness
    (hrank : RankOneRootReducednessStatement.{u})
    (hW : SplitMaximalTorusWeylRationalityStatement.{u})
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
    rw [RankOneCentralizerDetection.kernelCentralizer_torusHom_eq_top_of_rankOneReducedness
      hrank hG hT i hi hα]
    trivial
  obtain ⟨ν, ⟨h2, href⟩, -⟩ := hT.existsUnique_coroot_of_mem_kernelCentralizer _ α hα.1 m hflip hc
  refine ⟨normalizerPointsMap _ (RankOneCentralizerDetection.inclusion i hT α hα.1) i
    (RankOneCentralizerDetection.torusHom_comp i hT α hα.1) m, ν, h2, fun χ => ?_⟩
  rw [weylAction_normalizerPointsMap]
  exact href χ

/-- **Integral reflection data from rank-one reducedness and Weyl-group rationality.** For
a split maximal torus of a connected reductive group, the two explicit hypotheses provide, for
every actual root, a rational normalizing point and an integral coroot pairing to two with the
root, acting on characters by the reflection formula. -/
def reflectionData_of_rankOneReducedness
    (hrank : RankOneRootReducednessStatement.{u})
    (hW : SplitMaximalTorusWeylRationalityStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.2.1.mono
    RelativeRootReflectionData i :=
  haveI := hG.isAffineHom
  haveI := hi.2.1.mono
  { coroot := fun α =>
      Classical.choose (Classical.choose_spec
        (exists_reflection_of_rankOneReducedness hrank hW hG hT i hi α.property))
    representative := fun α => Classical.choose
      (exists_reflection_of_rankOneReducedness hrank hW hG hT i hi α.property)
    pair_self := fun α =>
      (Classical.choose_spec (Classical.choose_spec
        (exists_reflection_of_rankOneReducedness hrank hW hG hT i hi α.property))).1
    action := fun α =>
      (Classical.choose_spec (Classical.choose_spec
        (exists_reflection_of_rankOneReducedness hrank hW hG hT i hi α.property))).2 }

end SplitWeylRationality

/-- Rank-one reducedness suffices for the finite reduced root datum on the actual
character and cocharacter lattices of every split maximal torus. -/
theorem rootDatumExistence_of_rankOneReducedness
    (hrank : RankOneRootReducednessStatement.{u}) : RootDatumExistenceStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.2.1.mono
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi.2.1
  exact exists_rootDatum_of_reflectionData_of_finite_weylImage i hG hT
    (SplitWeylRationality.reflectionData_of_rankOneReducedness hrank
      splitMaximalTorusWeylRationality hG hT i hi)
    (rootReducedness_of_rankOne hrank dynamicCentralizerReductive k G hG T hT i hi)

end Langlands.GroupScheme
