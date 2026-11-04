import Langlands.Representation.Aubert.General.RationalAssociatedOppositeJacquetTransport
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityStatement
import Langlands.Representation.Aubert.General.UnitaryOppositeJacquet

/-! # Associated normalized Jacquet transport and conditional unitary support -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
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

local instance instRationalUnitaryAssociatedJacquetSupport1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (J : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = longestRep cs J)
  (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ)

/-- The actual normalized opposite Jacquet functor, pulled back along the
specified lift's Levi conjugation, is naturally isomorphic to associated
standard Jacquet restriction. -/
def associatedOppositeJacquetIso :
    jacquetFunctor.{u, v}
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν J ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ) ⋙
      conjugationFunctor (n : RationalPoint k G.X)⁻¹
        (fun x => by
          simpa only [inv_inv] using
            (associatedOpposite_mem_of_pointRootSigns
              i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
              J n hn ζ hζ x).2.1) ≅
    jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs J))
      (hU (associatedSubset cs J)) :=
  jacquetConjugationIso
    (opposite_isSemidirectDecomposition i ν hStandard hG hi hν J ζ hζ)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs J))
    (n : RationalPoint k G.X)⁻¹
    (fun x => by
      simpa only [inv_inv] using
        (associatedOpposite_mem_of_pointRootSigns
          i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
          J n hn ζ hζ x).2.1)
    (fun x => by
      simpa only [inv_inv] using
        (associatedOpposite_mem_of_pointRootSigns
          i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
          J n hn ζ hζ x).2.2)
    (isClosed_oppositeUnipotent_localField i ζ) (hU (associatedSubset cs J))

include hLength hSimple hMin hAssoc hRoots hn in
/-- The normalized isomorphism has the actual translation formula on classes. -/
theorem associatedOppositeJacquetIso_hom_mk
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (a : A) :
    SmoothRep.hom ((associatedOppositeJacquetIso
      i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
      hU J n hn ζ hζ).hom.app A)
        (Jacquet.Localization.mk A.representation (oppositeUnipotent i ζ) 1 a) =
      Jacquet.Localization.mk A.representation (unipotent i ν (associatedSubset cs J)) 1
        (A.representation (n : RationalPoint k G.X)⁻¹ a) :=
  rfl

variable [T2Space (RationalPoint k G.X)]

include hLength hSimple hMin hAssoc hRoots hn hζ in
/-- Under actual opposite Haar reciprocity, admissible unitarizable objects
have equivalent vanishing at the two associated standard Jacquet functors. -/
theorem unitary_jacquet_subsingleton_iff_associated
    (hHaar : RationalOppositeHaarReciprocityStatement.{u})
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (hA : A.IsAdmissible)
    (hunitary : IsUnitarizable A.representation) :
    Subsingleton ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J) (hU J)).obj A) ↔
    Subsingleton ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs J))
      (hU (associatedSubset cs J))).obj A) := by
  obtain ⟨g, hc, hBasis⟩ := rationalOppositeIwahoriBasisStatement
    k G hG T i hi ν hν hStandard J (hU J) ζ hζ
  have hδ := hHaar k G hG T i hi ν hν hStandard J (hU J) ζ hζ
  exact (unitary_jacquet_subsingleton_iff_opposite
    (unipotent i ν J) (levi i ν J) (oppositeUnipotent i ζ)
    (hU J) (isClosed_oppositeUnipotent_localField i ζ)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν J).levi_le_normalizer
    (opposite_isSemidirectDecomposition
      i ν hStandard hG hi hν J ζ hζ).levi_le_normalizer
    g hc hBasis hδ A hA hunitary).trans
      (associatedOppositeJacquet_subsingleton_iff
        i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
        hU J n hn ζ hζ A)

include hLength hSimple hMin hAssoc hRoots hn hζ in
/-- Support only at the original standard radical obstructs unitarity. -/
theorem not_isUnitarizable_of_associatedJacquet_asymmetry
    (hHaar : RationalOppositeHaarReciprocityStatement.{u})
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (hA : A.IsAdmissible)
    (hnonzero : Nontrivial ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J) (hU J)).obj A))
    (hzero : Subsingleton ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs J))
      (hU (associatedSubset cs J))).obj A)) :
    ¬ IsUnitarizable A.representation := by
  intro hunitary
  exact not_subsingleton_iff_nontrivial.mpr hnonzero
    ((unitary_jacquet_subsingleton_iff_associated
      i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
      hU J n hn ζ hζ hHaar A hA hunitary).mpr hzero)

include hLength hSimple hMin hAssoc hRoots hn hζ in
/-- Support only at the associated standard radical also obstructs unitarity. -/
theorem not_isUnitarizable_of_associatedJacquet_reverse_asymmetry
    (hHaar : RationalOppositeHaarReciprocityStatement.{u})
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)) (hA : A.IsAdmissible)
    (hzero : Subsingleton ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J) (hU J)).obj A))
    (hnonzero : Nontrivial ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs J))
      (hU (associatedSubset cs J))).obj A)) :
    ¬ IsUnitarizable A.representation := by
  intro hunitary
  exact not_subsingleton_iff_nontrivial.mpr hnonzero
    ((unitary_jacquet_subsingleton_iff_associated
      i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hRoots hStandard
      hU J n hn ζ hζ hHaar A hA hunitary).mp hzero)

end Langlands.Aubert.General.RationalPointFamily
