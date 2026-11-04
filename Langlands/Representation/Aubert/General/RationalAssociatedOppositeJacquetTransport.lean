import Langlands.Representation.Aubert.General.RationalAssociatedCocharacterTransport
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.Representation.Aubert.General.Conjugation

/-! # Opposite Jacquet transport from the actual point-root comparisons -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
  (hStandard : StandardCocharacterStatement.{u})

include hLength hSimple hMin hAssoc hG hi hν hRoots hStandard in
/-- The target's point-root comparisons and standard cocharacters give all-test
opposite transport, without a scheme Coxeter realization. -/
theorem associatedOpposite_standardGroups_of_pointRootSigns
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ) :
    let ns := (normalizerEquiv i hN).symm n
    (standardParabolic i ν (rootSet i ν (associatedSubset cs J)) =
      (Dynamic.parabolic
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ζ ≫ i))).comap
        (G.innerIso (ns : GroupScheme.rationalPoints G)).hom) ∧
    (standardLevi i ν (rootSet i ν (associatedSubset cs J)) =
      (standardLevi i ν (rootSet i ν J)).comap
        (G.innerIso (ns : GroupScheme.rationalPoints G)).hom) ∧
    (standardUnipotent i ν (rootSet i ν (associatedSubset cs J)) =
      (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ζ ≫ i))).comap
        (G.innerIso (ns : GroupScheme.rationalPoints G)).hom) := by
  let ns := (normalizerEquiv i hN).symm n
  let ξ := associatedOppositeCocharacter i ns ζ
  have hξ := isStandardCocharacter_associatedOpposite_of_pointRootSigns
    i ν hN hZ cs hLength hSimple hMin hAssoc hi.isSplitSubtorus.1 hRoots hν J n hn hζ
  have hStd := (hStandard k G hG T i hi ν hν
    (rootSet i ν (associatedSubset cs J)) (rootSet_subset i ν _)).2 ξ hξ
  have hStd0 := (hStandard k G hG T i hi ν hν
    (rootSet i ν J) (rootSet_subset i ν J)).2 ζ hζ
  have hM :
      (Dynamic.centralizer
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ζ ≫ i))).comap
        (G.innerIso (ns : GroupScheme.rationalPoints G)).hom =
      Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i) := by
    rw [← groupHom_cocharacterAut_associatedOppositeCocharacter i ns ζ,
      groupHom_cocharacterAut_comp]
    exact (Dynamic.centralizer_eq_comap_of_iso _ _).symm
  change
    (Dynamic.centralizer
      (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i))).comap _ = _ at hM
  rw [Dynamic.centralizer_inverseCocharacter, ← hStd0.2.1] at hM
  exact ⟨hStd.1.trans (parabolic_oppositeCocharacter_comap_innerIso i ns ζ).symm,
    hStd.2.1.trans hM.symm,
    hStd.2.2.trans (unipotent_oppositeCocharacter_comap_innerIso i ns ζ).symm⟩

include hLength hSimple hMin hAssoc hG hi hν hRoots hStandard in
/-- Every specified point-normalizer lift gives the literal associated/opposite
membership identities for the parabolic, Levi and radical. -/
theorem associatedOpposite_mem_of_pointRootSigns
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ)
    (x : RationalPoint k G.X) :
    (x ∈ parabolic i ν (associatedSubset cs J) ↔
      (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈
        oppositeParabolic i ζ) ∧
    (x ∈ levi i ν (associatedSubset cs J) ↔
      (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈ levi i ν J) ∧
    (x ∈ unipotent i ν (associatedSubset cs J) ↔
      (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈
        oppositeUnipotent i ζ) := by
  obtain ⟨hP, hM, hU⟩ := associatedOpposite_standardGroups_of_pointRootSigns
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard J n hn ζ hζ
  have hcoe : ((normalizerEquiv i hN).symm n : RationalPoint k G.X) = n :=
    congrArg Subtype.val ((normalizerEquiv i hN).apply_symm_apply n)
  constructor
  · change x ∈ (standardParabolic i ν (rootSet i ν (associatedSubset cs J))).rationalPoints ↔ _
    rw [hP, SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom, hcoe]
    rfl
  constructor
  · change x ∈ (standardLevi i ν (rootSet i ν (associatedSubset cs J))).rationalPoints ↔ _
    rw [hM, SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom, hcoe]
  · change x ∈ (standardUnipotent i ν (rootSet i ν (associatedSubset cs J))).rationalPoints ↔ _
    rw [hU, SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom, hcoe]
    rfl

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (J : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = longestRep cs J)
  (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ)

/-- Translation by the inverse specified lift identifies the actual normalized
opposite Jacquet carrier with the associated standard Jacquet carrier. -/
def associatedOppositeJacquetLinearEquiv
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) :
    ((jacquetFunctor (opposite_isSemidirectDecomposition i ν hStandard hG hi hν J ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)).obj A) ≃ₗ[ℂ]
    ((jacquetFunctor (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs J))
      (hU (associatedSubset cs J))).obj A) :=
  coinvariantsTranslateEquiv (n : RationalPoint k G.X)⁻¹
    (fun x => by
      simpa only [inv_inv] using
        (associatedOpposite_mem_of_pointRootSigns
          i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
          J n hn ζ hζ x).2.2) A.representation

include hLength hSimple hMin hAssoc hRoots hn in
/-- The equivalence retains the actual formula on coinvariant classes. -/
theorem associatedOppositeJacquetLinearEquiv_mk
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (v : A) :
    associatedOppositeJacquetLinearEquiv
      i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
      hU J n hn ζ hζ A (Jacquet.Localization.mk A.representation (oppositeUnipotent i ζ) 1 v) =
    Jacquet.Localization.mk A.representation (unipotent i ν (associatedSubset cs J)) 1
      (A.representation (n : RationalPoint k G.X)⁻¹ v) :=
  rfl

include hLength hSimple hMin hAssoc hRoots hn in
/-- Vanishing transfers between the actual opposite and associated normalized
Jacquet modules, for every smooth object. -/
theorem associatedOppositeJacquet_subsingleton_iff
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) :
    Subsingleton ((jacquetFunctor
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν J ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)).obj A) ↔
    Subsingleton ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs J))
      (hU (associatedSubset cs J))).obj A) := by
  let e := associatedOppositeJacquetLinearEquiv
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
    hU J n hn ζ hζ A
  constructor
  · intro h
    exact ⟨fun x y => e.symm.injective (h.elim _ _)⟩
  · intro h
    exact ⟨fun x y => e.injective (h.elim _ _)⟩

end LocalField

end Langlands.Aubert.General.RationalPointFamily
