import Langlands.GroupScheme.Rational.NestedParabolicLeviCone
import Langlands.GroupScheme.Rational.ParabolicIntrinsicNonnegCone
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer

/-! # Actual inner cocharacters and the nested nonnegative cone -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {G P M Q L PL : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {B A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  {q : Q ⟶ G} {l : L ⟶ Q} {a : A.toGrp ⟶ L}
  (fine : ParabolicRootPresentation p m b)
  (outer : ParabolicRootPresentation q l a)
  (pL : PL ⟶ L) (mL : M ⟶ PL)
  (hM : (mL ≫ pL) ≫ (l ≫ q) = m ≫ p)
  (hPL : SubgroupFunctor.range (pL ≫ (l ≫ q)) =
    SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range p)

/-- The fine defining split-component cocharacter in the original outer Levi. -/
def innerDefiningCocharacter : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L :=
  CommGroupScheme.groupHom fine.splitComponentCocharacter ≫ b ≫ mL ≫ pL

include hM in
/-- The constructed cocharacter has the original fine ambient image. -/
theorem innerDefiningCocharacter_comp :
    fine.innerDefiningCocharacter pL mL ≫ (l ≫ q) =
      CommGroupScheme.groupHom fine.splitComponentCocharacter ≫ b ≫ m ≫ p := by
  simpa only [innerDefiningCocharacter, Category.assoc] using
    congrArg (fun f => CommGroupScheme.groupHom fine.splitComponentCocharacter ≫ b ≫ f) hM

include outer hM hPL in
/-- Closed pullback identifies the original inner parabolic with its dynamic model. -/
theorem parabolic_eq_innerDefiningCocharacter :
    SubgroupFunctor.range pL = Dynamic.parabolic (fine.innerDefiningCocharacter pL mL) := by
  have hjc := outer.isCompatible.levi.isClosedSubgroup.comp
    outer.isCompatible.parabolic.isClosedSubgroup
  let := hjc.mono
  have : Mono (l ≫ q).hom.hom := Over.mono_of_mono_left _
  rw [SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf pL (l ≫ q)
    (SubgroupFunctor.range p) hPL, fine.parabolic_eq_splitComponentCocharacter]
  rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ (l ≫ q) hjc,
    fine.innerDefiningCocharacter_comp pL mL hM]

include outer hM in
/-- The same cocharacter centralizes exactly the supplied original common Levi. -/
theorem levi_eq_innerDefiningCocharacter :
    SubgroupFunctor.range (mL ≫ pL) =
      Dynamic.centralizer (fine.innerDefiningCocharacter pL mL) := by
  have hjc := outer.isCompatible.levi.isClosedSubgroup.comp
    outer.isCompatible.parabolic.isClosedSubgroup
  let := hjc.mono
  have : Mono (l ≫ q).hom.hom := Over.mono_of_mono_left _
  have hle : SubgroupFunctor.range (m ≫ p) ≤ SubgroupFunctor.range (l ≫ q) := by
    rw [← hM]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine ⟨y ≫ (mL ≫ pL).hom.hom, ?_⟩
    change (y ≫ (mL ≫ pL).hom.hom) ≫ (l ≫ q).hom.hom =
      y ≫ ((mL ≫ pL) ≫ (l ≫ q)).hom.hom
    simp only [Grp.comp_hom_hom, Category.assoc]
  have hrange : SubgroupFunctor.range ((mL ≫ pL) ≫ (l ≫ q)) =
      SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range (m ≫ p) := by
    rw [hM]
    apply le_antisymm
    · intro T x hx
      exact ⟨hle T hx, hx⟩
    · intro T x hx
      exact hx.2
  rw [SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf (mL ≫ pL) (l ≫ q)
    (SubgroupFunctor.range (m ≫ p)) hrange, fine.levi_eq_splitComponentCocharacter]
  rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup _ (l ≫ q) hjc,
    fine.innerDefiningCocharacter_comp pL mL hM]

include outer hM in
/-- The fine component factor still has its original image inside the outer Levi. -/
theorem fineComponent_comp_outerFineTorusFactor :
    CommGroupScheme.groupHom fine.data.f ≫
      fine.outerFineTorusFactor outer (mL ≫ pL) hM = b ≫ mL ≫ pL := by
  have hjc := outer.isCompatible.levi.isClosedSubgroup.comp
    outer.isCompatible.parabolic.isClosedSubgroup
  let := hjc.mono
  have : Mono (l ≫ q).hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono (l ≫ q).hom.hom).mp
  change (CommGroupScheme.groupHom fine.data.f ≫
      fine.outerFineTorusFactor outer (mL ≫ pL) hM ≫ (l ≫ q)).hom.hom =
    ((b ≫ mL ≫ pL) ≫ (l ≫ q)).hom.hom
  rw [fine.outerFineTorusFactor_comp outer (mL ≫ pL) hM,
    fine.isCompatible.factor_comp]
  congr 1
  simpa only [Category.assoc] using congrArg (fun f => (b ≫ f).hom) hM.symm

variable [IsAffineHom L.X.hom]

include outer hM hPL in
/-- The fine component cocharacter has the intrinsic positive support of every
supplied compatible inner presentation, by their common actual radical. -/
theorem positiveRelativeRoots_innerDefining_eq
    (inner : ParabolicRootPresentation pL mL b) :
    positiveRelativeRoots (b ≫ mL ≫ pL) fine.splitComponentCocharacter =
      inner.intrinsicPositiveRoots := by
  have := outer.isCompatible.levi.isConnectedReductive.smooth
  obtain ⟨N, n, hn, _⟩ := inner.isCompatible.levi.exists_unipotentRadical
  rw [inner.intrinsicPositiveRoots_eq_subgroupRelativeRoots hn]
  have hjc := outer.isCompatible.levi.isClosedSubgroup.comp
    outer.isCompatible.parabolic.isClosedSubgroup
  let := inner.isCompatible.parabolic.isClosedSubgroup.mono
  let := (inner.isCompatible.levi.isClosedSubgroup.comp
    inner.isCompatible.parabolic.isClosedSubgroup).mono
  have hrange := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    (fine.innerDefiningCocharacter pL mL)
    ⟨Over.mono_of_mono_left _,
      fine.parabolic_eq_innerDefiningCocharacter outer pL mL hM hPL⟩
    ⟨Over.mono_of_mono_left _,
      fine.levi_eq_innerDefiningCocharacter outer pL mL hM⟩
    inner.isCompatible.levi.isConnectedReductive hn
  rw [hrange]
  exact (RelativeRoot.subgroupRelativeRoots_dynamicUnipotent (b ≫ mL ≫ pL)
    inner.isCompatible.splitComponent.isCentralSplitTorus.1.1
    fine.splitComponentCocharacter).symm

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom]
  (hG : IsConnectedReductive G)
  (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)

include hG hP hM hPL in
/-- Every actual outer-Levi face generator is an intrinsic positive root of the
original inner parabolic, for every supplied compatible presentation. -/
theorem outerFaceRoot_restrict_mem_innerIntrinsicPositiveRoots
    (inner : ParabolicRootPresentation pL mL b)
    {alpha : characterLattice fine.data.T}
    (halpha : alpha ∈ simpleRelativeRoots
      (fine.outerFineTorusFactor outer (mL ≫ pL) hM) fine.data.ν)
    (hJ : alpha ∉ fine.data.J) :
    fine.data.f ≫ alpha ∈ inner.intrinsicPositiveRoots := by
  have hs := fine.simpleRelativeRoots_outerFineTorusFactor outer (mL ≫ pL) hM hG hP
  have hsimple : alpha ∈ simpleRelativeRoots fine.data.i fine.data.ν :=
    (hs ▸ halpha).1
  have hpos := fine.restrict_mem_intrinsicPositiveRoots hsimple hJ
  rw [← fine.positiveRelativeRoots_innerDefining_eq outer pL mL hM hPL inner]
  refine ⟨?_, hpos.2⟩
  rw [← fine.fineComponent_comp_outerFineTorusFactor outer pL mL hM]
  exact (rootRestriction fine.data.f
    (fine.outerFineTorusFactor outer (mL ≫ pL) hM)
    ⟨alpha, halpha.1.1, hpos.1.1⟩).property

include hG hP hM hPL in
/-- The actual outer-Levi face cone lies in every supplied inner nonnegative cone. -/
theorem outerFaceNonnegCone_subset_inner
    (inner : ParabolicRootPresentation pL mL b) :
    fine.outerFaceNonnegCone outer (mL ≫ pL) hM ⊆ inner.nonnegCone := by
  have hroot : restrictedSimpleRoots
      (fine.outerFineTorusFactor outer (mL ≫ pL) hM) fine.data.ν fine.data.J fine.data.f ⊆
      (RootCombination.nonnegCone inner.finite_restrictedRoots : Set (Vstar B)) := by
    rintro x ⟨alpha, ⟨halpha, hJ⟩, rfl⟩
    apply inner.one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots
      (relativeRootNegation k L outer.isCompatible.levi.isConnectedReductive
        inner.data.T inner.data.i inner.isCompatible.maximalSplit)
    exact fine.outerFaceRoot_restrict_mem_innerIntrinsicPositiveRoots
      outer pL mL hM hPL hG hP inner halpha hJ
  have hcone : RootCombination.nonnegCone
      (finite_restrictedSimpleRoots
        (fine.outerFineTorusFactor outer (mL ≫ pL) hM) fine.data.ν fine.data.J fine.data.f
        ((fine.isMaximalSplitTorus_outerFineTorusFactor outer (mL ≫ pL) hM).isSplitSubtorus.1.finite_simpleRelativeRoots _ _)) ≤
      RootCombination.nonnegCone inner.finite_restrictedRoots := by
    rw [RootCombination.nonnegCone_eq_hull]
    exact Submodule.span_le.mpr hroot
  exact hcone

include hG hP hM hPL in
/-- A fine nonnegative vector with zero actual outer restriction lies in every
supplied inner nonnegative cone. -/
theorem mem_innerNonnegCone_of_fine_mem_of_outerRestriction_eq_zero
    (inner : ParabolicRootPresentation pL mL b) {x : Vstar B}
    (hx : x ∈ fine.nonnegCone)
    (hzero : fine.outerComponentRestriction outer (mL ≫ pL) hM x = 0) :
    x ∈ inner.nonnegCone := by
  apply fine.outerFaceNonnegCone_subset_inner outer pL mL hM hPL hG hP inner
  exact (fine.mem_outerFaceNonnegCone_iff outer (mL ≫ pL) hM hG hP).mpr ⟨hx, hzero⟩

end Langlands.GroupScheme.ParabolicRootPresentation
