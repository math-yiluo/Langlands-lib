import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # The outer defining cocharacter in a fine parabolic presentation -/

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

/-- The original outer split component mapped into the fine presentation torus. -/
def outerComponentInFineTorus : A ⟶ fine.data.T :=
  fine.intermediateSplitComponentFactor (l ≫ q) (outerLeviClosed outer)
    i hi a outer.isCompatible.splitComponent.isCentralSplitTorus.isCentral
    outer.isCompatible.splitComponent.isCentralSplitTorus.1.1 ≫ fine.data.f

/-- This torus map retains the original outer split-component inclusion. -/
theorem outerComponentInFineTorus_comp :
    CommGroupScheme.groupHom (fine.outerComponentInFineTorus outer i hi) ≫ fine.data.i =
      a ≫ l ≫ q := by
  change (CommGroupScheme.groupHom
    (fine.intermediateSplitComponentFactor (l ≫ q) (outerLeviClosed outer)
      i hi a outer.isCompatible.splitComponent.isCentralSplitTorus.isCentral
      outer.isCompatible.splitComponent.isCentralSplitTorus.1.1) ≫
        CommGroupScheme.groupHom fine.data.f) ≫ fine.data.i = _
  rw [Category.assoc, fine.isCompatible.factor_comp]
  rw [← hi]
  have h := fine.intermediateSplitComponentFactor_comp (l ≫ q) (outerLeviClosed outer)
    i hi a outer.isCompatible.splitComponent.isCentralSplitTorus.isCentral
    outer.isCompatible.splitComponent.isCentralSplitTorus.1.1
  simpa only [Category.assoc] using congrArg (fun f : A.toGrp ⟶ L => f ≫ l ≫ q) h

/-- The original outer defining cocharacter, expressed on the fine maximal split torus. -/
def outerCocharacterInFineTorus : cocharacterLattice fine.data.T :=
  cocharacterMapInt (fine.outerComponentInFineTorus outer i hi)
    outer.splitComponentCocharacter

theorem outerCocharacterInFineTorus_comp :
    CommGroupScheme.groupHom (fine.outerCocharacterInFineTorus outer i hi) ≫ fine.data.i =
      CommGroupScheme.groupHom outer.splitComponentCocharacter ≫ a ≫ l ≫ q := by
  change (CommGroupScheme.groupHom outer.splitComponentCocharacter ≫
    CommGroupScheme.groupHom (fine.outerComponentInFineTorus outer i hi)) ≫
      fine.data.i = _
  rw [Category.assoc, fine.outerComponentInFineTorus_comp outer i hi]

/-- Its dynamic parabolic is the original outer parabolic on every test scheme. -/
theorem parabolic_eq_outerCocharacterInFineTorus :
    SubgroupFunctor.range q =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (fine.outerCocharacterInFineTorus outer i hi) ≫
          fine.data.i) := by
  rw [fine.outerCocharacterInFineTorus_comp outer i hi]
  exact outer.parabolic_eq_splitComponentCocharacter

/-- Its dynamic centralizer is the original outer Levi image. -/
theorem levi_eq_outerCocharacterInFineTorus :
    SubgroupFunctor.range (l ≫ q) =
      Dynamic.centralizer
        (CommGroupScheme.groupHom (fine.outerCocharacterInFineTorus outer i hi) ≫
          fine.data.i) := by
  rw [fine.outerCocharacterInFineTorus_comp outer i hi]
  exact outer.levi_eq_splitComponentCocharacter

variable (hG : IsConnectedReductive G) (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)

include hG hP

/-- Nesting forces the outer cocharacter to be dominant in the fine positive system. -/
theorem outerCocharacterInFineTorus_nonneg
    {α : characterLattice fine.data.T}
    (hα : α ∈ positiveRelativeRoots fine.data.i fine.data.ν) :
    0 ≤ latticePairing fine.data.T α (fine.outerCocharacterInFineTorus outer i hi) := by
  have hle := fine.isCompatible.minimal_le.trans hP
  rw [fine.parabolic_eq_outerCocharacterInFineTorus outer i hi] at hle
  exact (relativeRootSignInclusions k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit fine.data.ν
    (fine.outerCocharacterInFineTorus outer i hi)).1.mp hle α hα.1 hα.2.le

/-- The simple roots annihilated by the outer cocharacter in the fine presentation. -/
def outerSimpleRootFace : Set (characterLattice fine.data.T) :=
  simpleRootFace fine.data.i fine.data.ν (fine.outerCocharacterInFineTorus outer i hi)

omit hG hP in
theorem outerSimpleRootFace_subset :
    fine.outerSimpleRootFace outer i hi ⊆ simpleRelativeRoots fine.data.i fine.data.ν :=
  simpleRootFace_subset _ _ _

/-- The transported outer cocharacter is standard for precisely its zero face. -/
theorem isStandard_outerCocharacterInFineTorus :
    IsStandardCocharacter fine.data.i fine.data.ν
      (fine.outerSimpleRootFace outer i hi) (fine.outerCocharacterInFineTorus outer i hi) :=
  isStandardCocharacter_simpleRootFace _ _ fun _ hα =>
    fine.outerCocharacterInFineTorus_nonneg outer i hi hG hP
      (simpleRelativeRoots_subset_positive _ _ hα)

/-- The selected fine roots belong to the outer zero face. -/
theorem selected_subset_outerSimpleRootFace :
    fine.data.J ⊆ fine.outerSimpleRootFace outer i hi := by
  intro α hα
  have hs := fine.isCompatible.subset_simpleRoots hα
  refine ⟨hs, ?_⟩
  have hn := fine.outerCocharacterInFineTorus_nonneg outer i hi hG hP hs.1
  obtain ⟨ζ, hζ, hp, -⟩ := fine.isCompatible.realization
  have hle := hP
  rw [hp, fine.parabolic_eq_outerCocharacterInFineTorus outer i hi] at hle
  have hneg := relativeRootNegation k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit α hs.1.1
  have hz : 0 ≤ latticePairing fine.data.T (-α) ζ := by
    simp only [map_neg, LinearMap.neg_apply, hζ.2.1 α hα, neg_zero, le_refl]
  have hnn := (relativeRootSignInclusions k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit ζ
    (fine.outerCocharacterInFineTorus outer i hi)).1.mp hle (-α) hneg hz
  simp only [map_neg, LinearMap.neg_apply] at hnn
  omega

end Langlands.GroupScheme.ParabolicRootPresentation
