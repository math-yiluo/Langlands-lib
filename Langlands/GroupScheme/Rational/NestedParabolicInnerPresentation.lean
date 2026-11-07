import Langlands.GroupScheme.Rational.NestedParabolicInnerCone
import Langlands.GroupScheme.Rational.DynamicLeviParabolicTransfer
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsNegation
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.Representation.Exponents.LeviParabolicPreimageGeometry

/-! # Compatible inner presentations inherited from nested ambient data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Minimality descends through a supplied actual Levi decomposition when the
ambient minimal parabolic contains the original radical. -/
theorem IsMinimalParabolicFunctor.comap_levi_of_radical_le
    {k : Type u} [Field k]
    {G Q L U : GroupScheme (Spec (CommRingCat.of k))}
    (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    [IsIso (subgroupMultiplication l r)]
    {F : SubgroupFunctor G} (hF : IsMinimalParabolicFunctor F)
    (hU : SubgroupFunctor.range (r ≫ q) ≤ F)
    (hinner : IsParabolicFunctor (F.comap (l ≫ q))) :
    IsMinimalParabolicFunctor (F.comap (l ≫ q)) := by
  refine ⟨hinner, ?_⟩
  rintro F' ⟨C, c, hc, rfl⟩ hle
  let hn := hr.1.isNormal
  let e := LeviPreimage.inclusion l r hn c
  have hepar : IsParabolicSubgroup (e ≫ q) :=
    LeviPreimage.isParabolicSubgroup_ambient l r hn c q hq hl hr hc
  have hele : SubgroupFunctor.range (e ≫ q) ≤ F := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    let z := y ≫ e.hom.hom
    have hz : z ∈ (SubgroupFunctor.range e).carrier T := ⟨y, rfl⟩
    rw [SubgroupPreimage.range_inclusion] at hz
    change z ≫ (leviRetraction l r hn).hom.hom ∈ (SubgroupFunctor.range c).carrier T at hz
    rw [comp_leviRetraction] at hz
    have hlevi := hle T hz
    have hrad := hU T (SubgroupFunctor.mem_range.mpr
      ⟨radicalComponent l r z, rfl⟩)
    change z ≫ q.hom.hom ∈ F.carrier T
    rw [← leviComponent_mul_radicalComponent l r z, MonObj.mul_comp]
    exact (F.carrier T).mul_mem
      (by simpa only [SubgroupFunctor.mem_comap, Grp.comp_hom_hom, Category.assoc] using hlevi)
      (by simpa only [Grp.comp_hom_hom, Category.assoc] using hrad)
  have heq : SubgroupFunctor.range (e ≫ q) = F :=
    hF.2 _ ⟨_, e ≫ q, hepar, rfl⟩ hele
  have : Mono q.hom.hom := hq.isClosedSubgroup.mono_overHom
  have : Mono l.hom.hom := hl.isClosedSubgroup.mono_overHom
  have : Mono (l ≫ q).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hint := LeviPreimage.range_ambient_intersection l r hn c q
  rw [heq] at hint
  exact SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf c (l ≫ q) F
    (by simpa only [Category.assoc] using hint)

namespace ParabolicRootPresentation

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

/-- Actual inner presentation data retain the fine torus, generic cocharacter,
selected roots and component factor, using its lift to the original outer Levi. -/
def innerPresentationData : ParabolicRootPresentationData B L where
  T := fine.data.T
  i := fine.outerFineTorusFactor outer (mL ≫ pL) hM
  ν := fine.data.ν
  J := fine.data.J
  f := fine.data.f

include outer hM in
/-- The inherited generic parabolic is the closed inverse image of the
original fine generic minimal parabolic. -/
theorem innerGeneric_parabolic_eq_comap :
    Dynamic.parabolic (CommGroupScheme.groupHom fine.data.ν ≫
      fine.outerFineTorusFactor outer (mL ≫ pL) hM) =
      (Dynamic.parabolic (CommGroupScheme.groupHom fine.data.ν ≫ fine.data.i)).comap
        (l ≫ q) := by
  rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ (l ≫ q)
    (outer.isCompatible.levi.isClosedSubgroup.comp
      outer.isCompatible.parabolic.isClosedSubgroup), Category.assoc,
    fine.outerFineTorusFactor_comp outer (mL ≫ pL) hM]

variable (hG : IsConnectedReductive G)
  (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)

include outer hM hG hP in
/-- The original outer radical lies in the fine generic minimal parabolic. -/
theorem range_outerRadical_le_fineMinimal
    {U : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ Q}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    SubgroupFunctor.range (r ≫ q) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom fine.data.ν ≫ fine.data.i) := by
  have := hG.smooth
  rw [outer.range_comp_radical_eq hr,
    ← fine.outerCocharacterInFineTorus_comp outer (mL ≫ pL) hM]
  apply unipotent_le_parabolic_of_parabolic_le relativeRootSignInclusions
    relativeRootNegation hG fine.isCompatible.maximalSplit
  rw [← fine.parabolic_eq_outerCocharacterInFineTorus outer (mL ≫ pL) hM]
  exact fine.isCompatible.minimal_le.trans hP

include outer hM in
/-- The inherited standard cocharacter is the original inner defining cocharacter. -/
theorem innerPresentationData_defining_comp :
    CommGroupScheme.groupHom
        (RealTorusSpace.cocharacterMapInt fine.data.f fine.splitComponentCocharacter) ≫
      fine.outerFineTorusFactor outer (mL ≫ pL) hM =
        fine.innerDefiningCocharacter pL mL := by
  change (CommGroupScheme.groupHom fine.splitComponentCocharacter ≫
    CommGroupScheme.groupHom fine.data.f) ≫ _ = _
  rw [Category.assoc, fine.fineComponent_comp_outerFineTorusFactor outer pL mL hM]
  rfl

variable [IsAffineHom L.X.hom]

include hM hG hP in
/-- Minimality of the inherited inner generic parabolic is derived from the
original radical and Levi decomposition, without a structural correspondence premise. -/
theorem innerGeneric_isMinimal
    {U : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ Q}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    [IsIso (subgroupMultiplication l r)] :
    IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom fine.data.ν ≫
      fine.outerFineTorusFactor outer (mL ≫ pL) hM)) := by
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let χ := CommGroupScheme.groupHom fine.data.ν ≫
    fine.outerFineTorusFactor outer (mL ≫ pL) hM
  have hpar : IsParabolicFunctor (Dynamic.parabolic χ) := by
    refine ⟨_, Dynamic.Affine.parabolicHom χ, ?_,
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2⟩
    exact isParabolicSubgroup_of_range_eq_dynamicParabolic
      outer.isCompatible.levi.isConnectedReductive _
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ) χ
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2
  rw [fine.innerGeneric_parabolic_eq_comap outer pL mL hM] at ⊢
  apply fine.isCompatible.minimal.comap_levi_of_radical_le q l r
    outer.isCompatible.parabolic outer.isCompatible.levi hr
    (fine.range_outerRadical_le_fineMinimal outer pL mL hM hG hP hr)
  rwa [← fine.innerGeneric_parabolic_eq_comap outer pL mL hM]

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom]

include hG hP in
/-- The fine selected roots remain simple in the original outer Levi. -/
theorem innerPresentationData_subset_simpleRoots :
    fine.data.J ⊆ simpleRelativeRoots
      (fine.outerFineTorusFactor outer (mL ≫ pL) hM) fine.data.ν := by
  rw [fine.simpleRelativeRoots_outerFineTorusFactor outer (mL ≫ pL) hM hG hP]
  exact fine.selected_subset_outerSimpleRootFace outer (mL ≫ pL) hM hG hP

include hG hP in
/-- The fine component cocharacter is standard for the inherited inner data. -/
theorem innerPresentationData_isStandard :
    IsStandardCocharacter (fine.outerFineTorusFactor outer (mL ≫ pL) hM)
      fine.data.ν fine.data.J
      (RealTorusSpace.cocharacterMapInt fine.data.f fine.splitComponentCocharacter) := by
  refine ⟨fine.innerPresentationData_subset_simpleRoots outer pL mL hM hG hP,
    fine.isStandard_splitComponentCocharacter.2.1, ?_⟩
  intro α hα hJ
  rw [fine.simpleRelativeRoots_outerFineTorusFactor outer (mL ≫ pL) hM hG hP] at hα
  exact fine.isStandard_splitComponentCocharacter.2.2 α hα.1 hJ


/-- A compatible presentation for the original inner maps, inherited from the
supplied nested ambient presentations and the original outer Levi decomposition. -/
def innerPresentation
    (hPL : SubgroupFunctor.range (pL ≫ (l ≫ q)) =
      SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range p)
    (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
    (hb : IsSplitComponent b)
    {U : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ Q}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    [IsIso (subgroupMultiplication l r)] : ParabolicRootPresentation pL mL b := by
  let ξ := RealTorusSpace.cocharacterMapInt fine.data.f fine.splitComponentCocharacter
  have hstd := fine.innerPresentationData_isStandard outer pL mL hM hG hP
  have heq := standard_eq_dynamic_of_relativeRootNegation relativeRootNegation k L
    outer.isCompatible.levi.isConnectedReductive fine.data.T
    (fine.outerFineTorusFactor outer (mL ≫ pL) hM)
    (fine.isMaximalSplitTorus_outerFineTorusFactor outer (mL ≫ pL) hM)
    fine.data.ν (fine.isGenericCocharacter_outerFineTorusFactor outer (mL ≫ pL) hM)
    fine.data.J ξ hstd
  change standardParabolic _ _ _ = Dynamic.parabolic
      (CommGroupScheme.groupHom
        (RealTorusSpace.cocharacterMapInt fine.data.f fine.splitComponentCocharacter) ≫ _) ∧
    standardLevi _ _ _ = Dynamic.centralizer _ ∧ _ at heq
  rw [fine.innerPresentationData_defining_comp outer pL mL hM] at heq
  have hpar := fine.parabolic_eq_innerDefiningCocharacter outer pL mL hM hPL
  have hlevi := fine.levi_eq_innerDefiningCocharacter outer pL mL hM
  refine ⟨fine.innerPresentationData outer pL mL hM,
    { parabolic := hpL
      levi := hmL
      splitComponent := hb
      maximalSplit := fine.isMaximalSplitTorus_outerFineTorusFactor outer (mL ≫ pL) hM
      generic := fine.isGenericCocharacter_outerFineTorusFactor outer (mL ≫ pL) hM
      subset_simpleRoots := hstd.1
      parabolic_eq := hpar.trans heq.1.symm
      levi_eq := hlevi.trans heq.2.1.symm
      factor_comp := fine.fineComponent_comp_outerFineTorusFactor outer pL mL hM
      minimal := fine.innerGeneric_isMinimal outer pL mL hM hG hP hr
      minimal_le := ?_
      realization := ?_ }⟩
  · change Dynamic.parabolic (CommGroupScheme.groupHom fine.data.ν ≫
        fine.outerFineTorusFactor outer (mL ≫ pL) hM) ≤ SubgroupFunctor.range pL
    have hjc := outer.isCompatible.levi.isClosedSubgroup.comp
      outer.isCompatible.parabolic.isClosedSubgroup
    let := hjc.mono
    have : Mono (l ≫ q).hom.hom := Over.mono_of_mono_left _
    rw [fine.innerGeneric_parabolic_eq_comap outer pL mL hM,
      SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf pL (l ≫ q)
        (SubgroupFunctor.range p) hPL]
    intro T x hx
    exact fine.isCompatible.minimal_le T hx
  · refine ⟨ξ, hstd, ?_, ?_⟩
    · change SubgroupFunctor.range pL = Dynamic.parabolic
        (CommGroupScheme.groupHom
          (RealTorusSpace.cocharacterMapInt fine.data.f fine.splitComponentCocharacter) ≫
          fine.outerFineTorusFactor outer (mL ≫ pL) hM)
      rw [fine.innerPresentationData_defining_comp outer pL mL hM]
      exact hpar
    · change SubgroupFunctor.range (mL ≫ pL) = Dynamic.centralizer
        (CommGroupScheme.groupHom
          (RealTorusSpace.cocharacterMapInt fine.data.f fine.splitComponentCocharacter) ≫
          fine.outerFineTorusFactor outer (mL ≫ pL) hM)
      rw [fine.innerPresentationData_defining_comp outer pL mL hM]
      exact hlevi

end ParabolicRootPresentation

end Langlands.GroupScheme
