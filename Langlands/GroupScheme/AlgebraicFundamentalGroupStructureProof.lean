import Langlands.GroupScheme.AlgebraicFundamentalGroupStatement
import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugatorExistence
import Langlands.GroupScheme.SimplyConnected.DerivedCoverMaximalTorusPreimageReduction
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.CommutativeSubgroupIntersectionBaseChange
import Langlands.GroupScheme.CentralIsogeny.TorusRestriction
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear

/-! # Structure of the algebraic fundamental group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Choice

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} (a : Choice k G)

set_option maxHeartbeats 800000 in
/-- The actual preimage inclusion is a maximal torus of the simply connected cover. -/
theorem scInclusion_isMaximalTorus : IsMaximalTorus a.scInclusion := by
  have hclosed : IsClosedSubgroup a.scInclusion :=
    isClosedSubgroup_subgroupIntersectionFst _ a.isMaximal.2.1
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let Tb := (CommGroupScheme.baseChange b).obj a.scTorus
  obtain ⟨A, j, f, hA, hj, hself, hcomm⟩ :=
    exists_selfCentralizing_sourceTorus_after_fieldExtension (K := K)
      maximalTorusCentralizer derivedMaximalSplitTorus a.isCover a.isMaximal
  have hjmax : IsMaximalTorus j :=
    isMaximalTorus_of_torusCentralizer_eq hA hj hself
  have hcomm' : j ≫ B.map (a.covering ≫ a.derivedInclusion) =
      f ≫ B.map a.inclusion := by
    simpa only [Functor.map_comp, Category.assoc] using hcomm
  let l : A.toGrp ⟶ Tb.toGrp :=
    pullback.lift j f hcomm' ≫
      (subgroupIntersectionBaseChangeIso b
        (a.covering ≫ a.derivedInclusion) a.inclusion).inv
  have hl : l ≫ B.map a.scInclusion = j := by
    change (pullback.lift j f hcomm' ≫
      (PreservesPullback.iso B (a.covering ≫ a.derivedInclusion) a.inclusion).inv) ≫
        B.map (pullback.fst (a.covering ≫ a.derivedInclusion) a.inclusion) = j
    rw [Category.assoc, PreservesPullback.iso_inv_fst, pullback.lift_fst]
  have hTb : IsTorus Tb.toGrp := a.scPreimage_isTorus.baseChange
  have : IsIso l := hjmax.2.2 Tb (B.map a.scInclusion) l hTb (hclosed.baseChange b) hl
  apply IsMaximalTorus.of_baseChange (K := K) hclosed
  apply (IsMaximalTorus.iso_comp_iff (T' := A) (T := Tb) (asIso l)
    (B.map a.scInclusion)).mp
  change IsMaximalTorus (T := A) (l ≫ B.map a.scInclusion)
  rw [hl]
  exact hjmax

/-- The actual projection from the preimage torus to the original torus is finite. -/
theorem scToTorus_isFinite :
    IsFinite (CommGroupScheme.groupHom a.scToTorus).hom.hom.left := by
  have : IsFinite a.covering.hom.hom.left :=
    a.isCover.isSimplyConnectedCover.isCentralIsogeny.isFinite
  have : IsClosedImmersion a.derivedInclusion.hom.hom.left :=
    a.isCover.isDerivedSubgroup.1
  have hfinite : IsFinite (a.covering ≫ a.derivedInclusion).hom.hom.left := by
    change IsFinite (a.covering.hom.hom.left ≫ a.derivedInclusion.hom.hom.left)
    infer_instance
  exact MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme
      (a.covering ≫ a.derivedInclusion) a.inclusion) hfinite

/-- The actual cocharacter map is injective after every field extension. -/
theorem corootMap_injective (E : Type u) [Field E] [Algebra k E] :
    Function.Injective (a.corootMap E) := by
  have : IsFinite (CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus)).hom.hom.left := by
    change IsFinite ((GroupScheme.baseChange (algebraBaseMap k E)).map
      (CommGroupScheme.groupHom a.scToTorus)).hom.hom.left
    exact MorphismProperty.of_isPullback
      (baseChange_map_isPullback (algebraBaseMap k E)
        (CommGroupScheme.groupHom a.scToTorus)).flip a.scToTorus_isFinite
  exact cocharacterMapInt_injective_of_isFinite
    ((CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus)

/-- The cocharacter quotient is finitely generated over the integers. -/
theorem atChoice_finite (E : Type u) [Field E] [Algebra k E] [IsSepClosure k E] :
    Module.Finite ℤ (a.atChoice E) := by
  have : Module.Finite ℤ (a.lattice E) :=
    (isSplitTorus_baseChange_of_isSepClosure a.torus a.isMaximal.1).finite_cocharacterLattice
  exact Module.Finite.of_surjective (a.projection E) (a.corootImage E).mkQ_surjective

end Choice

/-- KP Construction 11.3.1: maximal preimage, injective cocharacters and finite generation. -/
theorem algebraicFundamentalGroupStructure :
    AlgebraicFundamentalGroupStructureStatement.{u} := by
  intro k E _ _ _ _ G _ a
  exact ⟨a.scInclusion_isMaximalTorus, a.corootMap_injective E, a.atChoice_finite E⟩

end Langlands.GroupScheme.AlgebraicFundamentalGroup
