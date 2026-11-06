import Langlands.GroupScheme.Rational.ParabolicRootPresentationExistenceReduction
import Langlands.Representation.Aubert.General.RationalPointFamily

/-! # A simultaneous standard presentation of an actual dynamic triple -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Aubert.General

/-- An actual torus and finite simple-root index presenting the original
dynamic parabolic, Levi and radical simultaneously, on every test scheme. -/
structure DynamicStandardPresentation
    (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of F))
  torusHom : torus.toGrp ⟶ G
  maximal : IsMaximalSplitTorus torusHom
  original : cocharacterLattice torus
  factor : CommGroupScheme.groupHom original ≫ torusHom = χ
  direction : cocharacterLattice torus
  generic : IsGenericCocharacter torusHom direction
  index : Finset (RationalPointFamily.SimpleRoot torusHom direction)
  standard : IsStandardCocharacter torusHom direction
    (RationalPointFamily.rootSet torusHom direction index) original
  parabolic_eq : standardParabolic torusHom direction
    (RationalPointFamily.rootSet torusHom direction index) = Dynamic.parabolic χ
  levi_eq : standardLevi torusHom direction
    (RationalPointFamily.rootSet torusHom direction index) = Dynamic.centralizer χ
  unipotent_eq : standardUnipotent torusHom direction
    (RationalPointFamily.rootSet torusHom direction index) = Dynamic.unipotent χ

/-- Choose a simultaneous standard presentation of any dynamic triple.
Only the published standard-cocharacter statement is retained as structural
input; generic refinement and finite actual-root indexing are constructed. -/
def dynamicStandardPresentation
    (hStandard : StandardCocharacterStatement.{u})
    (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F)))
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    haveI := hG.isAffineHom
    DynamicStandardPresentation F G χ := by
  haveI := hG.isAffineHom
  apply Classical.choice
  have : Nonempty (DynamicStandardPresentation F G χ) := by
    have := hG.smooth
    obtain ⟨T, i, ξ, hi, hξ⟩ := cocharacterMaximalSplitTorus F G χ
    obtain ⟨ν, hν, hsupport⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter_refining i ξ
    classical
    let : Fintype (RationalPointFamily.SimpleRoot i ν) :=
      simpleRelativeRootFintypeOfIsSplitTorus i hi.isSplitSubtorus.1 ν
    let I : Finset (RationalPointFamily.SimpleRoot i ν) :=
      Finset.univ.filter (fun α => latticePairing T α.val ξ = 0)
    have hI : RationalPointFamily.rootSet i ν I = simpleRootFace i ν ξ := by
      ext α
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.property, (Finset.mem_filter.mp ha).2⟩
      · intro hα
        exact ⟨⟨α, hα.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα.2⟩, rfl⟩
    have hstandard : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ξ := by
      rw [hI]
      exact isStandardCocharacter_simpleRootFace i ν (fun α hα =>
        hsupport α (simpleRelativeRoots_subset_positive i ν hα).1
          (simpleRelativeRoots_subset_positive i ν hα).2.le)
    have hcompare := (hStandard F G hG T i hi ν hν
      (RationalPointFamily.rootSet i ν I) (RationalPointFamily.rootSet_subset i ν I)).2
        ξ hstandard
    rw [hξ] at hcompare
    exact ⟨
      { torus := T
        torusHom := i
        maximal := hi
        original := ξ
        factor := hξ
        direction := ν
        generic := hν
        index := I
        standard := hstandard
        parabolic_eq := hcompare.1
        levi_eq := hcompare.2.1
        unipotent_eq := hcompare.2.2 }⟩
  exact this

end Langlands.Aubert.General
