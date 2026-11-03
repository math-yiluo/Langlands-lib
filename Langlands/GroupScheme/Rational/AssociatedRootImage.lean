import Langlands.Representation.Aubert.General.RationalAssociatedLeviRestriction
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Group.RelativeWeylAssociatedIndexing

/-! # Actual character images of associated finite root subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

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

include hLength hSimple

/-- The forward associated label is the actual positive character image,
with its sign fixed by the length comparison. -/
theorem weylCharacterAction_associatedSimpleEquiv
    (J : Finset (SimpleRoot i ν)) (a : associatedSubset cs J) :
    weylCharacterAction i hN hZ (longestRep cs J) (a : SimpleRoot i ν).val =
      (associatedSimpleEquiv cs J a : SimpleRoot i ν).val := by
  have hpos : weylCharacterAction i hN hZ (longestRep cs J)
      (a : SimpleRoot i ν).val ∈ positiveRelativeRoots i ν := by
    apply (hLength _ (a : SimpleRoot i ν)).mp
    apply (mem_positiveSimpleSet cs _ _).mp
    rw [positiveSimpleSet_longestRep]
    exact a.property
  exact (hSimple _ (a : SimpleRoot i ν)
    (associatedSimpleEquiv cs J a : SimpleRoot i ν) hpos).mp
      (associatedSimpleEquiv_conj cs J a)

/-- The equivalence of actual character subsets is induced by the longest
element's character-lattice automorphism, rather than just reflection labels. -/
def associatedRootSetEquiv
    (J : Finset (SimpleRoot i ν)) (I : Finset (associatedSubset cs J)) :
    rootSet i ν (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))) ≃
      rootSet i ν
        ((associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J))) :=
  ((weylCharacterAction i hN hZ (longestRep cs J)).toEquiv.image _).trans
    (Set.equivOfEq (rootSet_associatedFinsetEquiv i ν hN hZ cs hLength hSimple J I))

@[simp]
theorem associatedRootSetEquiv_apply
    (J : Finset (SimpleRoot i ν)) (I : Finset (associatedSubset cs J))
    (α : rootSet i ν
      (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J)))) :
    (associatedRootSetEquiv i ν hN hZ cs hLength hSimple J I α :
      characterLattice T) =
      weylCharacterAction i hN hZ (longestRep cs J) (α : characterLattice T) :=
  rfl

/-- The image formula uses the actual scheme normalizer point corresponding
to every point-normalizer lift of the specified longest representative. -/
theorem weylAction_image_associatedFinsetEquiv
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (I : Finset (associatedSubset cs J)) :
    weylAction i ((normalizerEquiv i hN).symm n) ''
        rootSet i ν (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))) =
      rootSet i ν
        ((associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J))) := by
  rw [← weylCharacterAction_point_mk i hN hZ, hn]
  exact rootSet_associatedFinsetEquiv i ν hN hZ cs hLength hSimple J I

end Langlands.Aubert.General.RationalPointFamily
