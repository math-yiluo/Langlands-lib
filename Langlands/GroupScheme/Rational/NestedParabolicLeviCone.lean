import Langlands.GroupScheme.Rational.NestedParabolicLeviRoots
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation

/-! # The nested Levi face of the fine nonnegative root cone -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {G P M Q L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {B A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  {q : Q ⟶ G} {l : L ⟶ Q} {a : A.toGrp ⟶ L}
  (fine : ParabolicRootPresentation p m b)
  (outer : ParabolicRootPresentation q l a)
  (i : M ⟶ L) (hi : i ≫ l ≫ q = m ≫ p)

include outer in
private theorem outerLeviClosed : IsClosedSubgroup (l ≫ q) :=
  outer.isCompatible.levi.isClosedSubgroup.comp outer.isCompatible.parabolic.isClosedSubgroup

/-- Real character restriction from the specified fine component to the outer one. -/
def outerComponentRestriction : Vstar B →ₗ[ℝ] Vstar A :=
  rationalCharacterRestrictReal (CommGroupScheme.groupHom
    (fine.intermediateSplitComponentFactor (l ≫ q) (outerLeviClosed outer)
      i hi a outer.isCompatible.splitComponent.isCentralSplitTorus.isCentral
      outer.isCompatible.splitComponent.isCentralSplitTorus.1.1))

/-- On a fine root vector, this is restriction along the original outer component. -/
theorem outerComponentRestriction_restrictedRootVector (alpha : characterLattice fine.data.T) :
    fine.outerComponentRestriction outer i hi (restrictedRootVector fine.data.f alpha) =
      restrictedRootVector (fine.outerComponentInFineTorus outer i hi) alpha := by
  rfl

/-- The torus map into the actual outer Levi still gives its original component map. -/
theorem outerComponentInFineTorus_comp_outerFineTorusFactor :
    CommGroupScheme.groupHom (fine.outerComponentInFineTorus outer i hi) ≫
      fine.outerFineTorusFactor outer i hi = a := by
  let := (outerLeviClosed outer).mono
  have : Mono (l ≫ q).hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono (l ≫ q).hom.hom).mp
  change (CommGroupScheme.groupHom (fine.outerComponentInFineTorus outer i hi) ≫
      fine.outerFineTorusFactor outer i hi ≫ (l ≫ q)).hom.hom = (a ≫ (l ≫ q)).hom.hom
  rw [fine.outerFineTorusFactor_comp outer i hi,
    fine.outerComponentInFineTorus_comp outer i hi]

variable [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]

/-- Roots of the original outer Levi vanish on its original central split component. -/
theorem outerRoot_restrict_eq_zero
    {alpha : characterLattice fine.data.T}
    (halpha : alpha ∈ relativeRoots (fine.outerFineTorusFactor outer i hi)) :
    fine.outerComponentInFineTorus outer i hi ≫ alpha = 0 := by
  apply root_restrict_eq_zero_of_isCentral (fine.outerFineTorusFactor outer i hi)
    (fine.outerComponentInFineTorus outer i hi)
    outer.isCompatible.splitComponent.isCentralSplitTorus.1.1
  · rw [fine.outerComponentInFineTorus_comp_outerFineTorusFactor outer i hi]
    exact outer.isCompatible.splitComponent.isCentralSplitTorus.isCentral
  · exact halpha

/-- The nonnegative cone using the actual outer-Levi roots, with the fine selected
roots and fine component factor retained. -/
def outerFaceNonnegCone : Set (Vstar B) :=
  restrictedRootNonnegCone (fine.outerFineTorusFactor outer i hi) fine.data.ν fine.data.J
    fine.data.f
    ((fine.isMaximalSplitTorus_outerFineTorusFactor outer i hi).isSplitSubtorus.1.finite_simpleRelativeRoots
      (fine.outerFineTorusFactor outer i hi) fine.data.ν)

omit [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom] in
/-- Evaluation after outer restriction measures the transported defining cocharacter. -/
theorem outerComponentEvaluation_restrictedRootVector
    (alpha : characterLattice fine.data.T) :
    outer.splitComponentEvaluation
        (fine.outerComponentRestriction outer i hi (restrictedRootVector fine.data.f alpha)) =
      (latticePairing fine.data.T alpha (fine.outerCocharacterInFineTorus outer i hi) : ℝ) := by
  rw [fine.outerComponentRestriction_restrictedRootVector outer i hi,
    restrictedRootVector_eq_tmul, outer.splitComponentEvaluation_tmul, one_mul]
  rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt]
  rfl

variable [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
  (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)

include hG hP

/-- The actual outer-Levi face cone is the fine cone intersected with the kernel
of restriction to the original outer split component. -/
theorem mem_outerFaceNonnegCone_iff {x : Vstar B} :
    x ∈ fine.outerFaceNonnegCone outer i hi ↔
      x ∈ fine.nonnegCone ∧ fine.outerComponentRestriction outer i hi x = 0 := by
  classical
  have hsimple := fine.simpleRelativeRoots_outerFineTorusFactor outer i hi hG hP
  have hsubsimple : simpleRelativeRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν ⊆
      simpleRelativeRoots fine.data.i fine.data.ν := by
    rw [hsimple]
    exact fine.outerSimpleRootFace_subset outer i hi
  have hfinL := (fine.isMaximalSplitTorus_outerFineTorusFactor outer i hi).isSplitSubtorus.1.finite_simpleRelativeRoots
    (fine.outerFineTorusFactor outer i hi) fine.data.ν
  constructor
  · intro hx
    have hsubset :
        restrictedSimpleRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν
          fine.data.J fine.data.f ⊆ fine.restrictedRoots := by
      rintro z ⟨alpha, ⟨halpha, hJ⟩, rfl⟩
      exact ⟨alpha, ⟨hsubsimple halpha, hJ⟩, rfl⟩
    have hcone : RootCombination.nonnegCone
        (finite_restrictedSimpleRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν
          fine.data.J fine.data.f hfinL) ≤
        RootCombination.nonnegCone fine.finite_restrictedRoots := by
      rw [RootCombination.nonnegCone_eq_hull, RootCombination.nonnegCone_eq_hull]
      exact Submodule.span_mono hsubset
    refine ⟨hcone hx, ?_⟩
    obtain ⟨c, hc, rfl⟩ := hx
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro z hz
    obtain ⟨alpha, ⟨halpha, hJ⟩, rfl⟩ :=
      (finite_restrictedSimpleRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν
        fine.data.J fine.data.f hfinL).mem_toFinset.mp hz
    rw [map_smul, fine.outerComponentRestriction_restrictedRootVector outer i hi]
    have hzroot : restrictedRootVector (fine.outerComponentInFineTorus outer i hi) alpha = 0 := by
      rw [restrictedRootVector_eq_tmul,
        fine.outerRoot_restrict_eq_zero outer i hi halpha.1.1, tmul_zero]
    rw [hzroot, smul_zero]
  · rintro ⟨hx, hzero⟩
    let hS : (simpleRelativeRoots fine.data.i fine.data.ν \ fine.data.J).Finite :=
      fine.finite_simpleRoots.sdiff
    let s := hS.toFinset
    let hK : (fine.outerSimpleRootFace outer i hi \ fine.data.J).Finite :=
      (fine.finite_simpleRoots.subset (fine.outerSimpleRootFace_subset outer i hi)).sdiff
    let t := hK.toFinset
    have hs : (↑s : Set (characterLattice fine.data.T)) =
        simpleRelativeRoots fine.data.i fine.data.ν \ fine.data.J := hS.coe_toFinset
    have ht : (↑t : Set (characterLattice fine.data.T)) =
        simpleRelativeRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν \ fine.data.J := by
      rw [hsimple]
      exact hK.coe_toFinset
    obtain ⟨c, hc, hsum⟩ := (mem_restrictedRootNonnegCone_iff_roots
      fine.data.i fine.data.ν fine.data.J fine.data.f fine.finite_simpleRoots s hs).mp hx
    have hnonneg : ∀ alpha ∈ s,
        0 ≤ c alpha *
          (latticePairing fine.data.T alpha
            (fine.outerCocharacterInFineTorus outer i hi) : ℝ) := by
      intro alpha halpha
      have ha : alpha ∈ simpleRelativeRoots fine.data.i fine.data.ν \ fine.data.J := by
        exact hs ▸ halpha
      exact mul_nonneg (hc alpha halpha) (by
        exact_mod_cast fine.outerCocharacterInFineTorus_nonneg outer i hi hG hP ha.1.1)
    have hsumzero : ∑ alpha ∈ s, c alpha *
        (latticePairing fine.data.T alpha
          (fine.outerCocharacterInFineTorus outer i hi) : ℝ) = 0 := by
      have heval := congrArg
        (fun y => outer.splitComponentEvaluation (fine.outerComponentRestriction outer i hi y))
        hsum
      simpa only [map_sum, map_smul, smul_eq_mul,
        fine.outerComponentEvaluation_restrictedRootVector outer i hi, hzero, map_zero] using heval
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumzero
    have hts : t ⊆ s := by
      intro alpha halpha
      have ha : alpha ∈ fine.outerSimpleRootFace outer i hi \ fine.data.J :=
        hK.mem_toFinset.mp halpha
      exact hS.mem_toFinset.mpr ⟨ha.1.1, ha.2⟩
    apply (mem_restrictedRootNonnegCone_iff_roots
      (fine.outerFineTorusFactor outer i hi) fine.data.ν fine.data.J fine.data.f hfinL t ht).mpr
    refine ⟨c, fun alpha halpha => hc alpha (hts halpha), ?_⟩
    calc
      ∑ alpha ∈ t, c alpha • restrictedRootVector fine.data.f alpha =
          ∑ alpha ∈ s, c alpha • restrictedRootVector fine.data.f alpha := by
        apply Finset.sum_subset hts
        intro alpha halpha hnot
        have ha := hS.mem_toFinset.mp halpha
        have hpair : latticePairing fine.data.T alpha
            (fine.outerCocharacterInFineTorus outer i hi) ≠ 0 := by
          intro hz
          exact hnot (hK.mem_toFinset.mpr ⟨⟨ha.1, hz⟩, ha.2⟩)
        have hczero : c alpha = 0 :=
          (mul_eq_zero.mp (hterms alpha halpha)).resolve_right (by exact_mod_cast hpair)
        rw [hczero, zero_smul]
      _ = x := hsum

end Langlands.GroupScheme.ParabolicRootPresentation
