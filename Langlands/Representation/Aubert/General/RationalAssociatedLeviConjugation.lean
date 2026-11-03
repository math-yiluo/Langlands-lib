import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Representation.Aubert.General.JacquetTarget
import Langlands.GroupScheme.Rational.StandardLeviConjugationStatement

/-! # Actual associated-Levi transport from the named structural statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.RationalSpan

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)

/-- Transport of the actual character sets transports their exact rational
encodings in the relative root span. This is not an assertion about spans. -/
theorem relativeRootSubset_image_of_character_image
    {J J' : Set (characterLattice T)} (hJ' : J' ⊆ relativeRoots i)
    (n : normalizerPoints i) (h : weylAction i n '' J' = J) :
    relativeWeylAction i (QuotientGroup.mk n) ''
        {x : relativeRootSpan i | (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} =
      {x : relativeRootSpan i | (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J} := by
  ext x
  constructor
  · rintro ⟨y, ⟨α, hα, hαy⟩, rfl⟩
    refine ⟨weylAction i n α, h ▸ Set.mem_image_of_mem _ hα, ?_⟩
    change toRat (weylAction i n α) = ratAut (weylAction i n) y
    rw [← hαy]
    rfl
  · rintro ⟨β, hβ, hβx⟩
    obtain ⟨α, hα, rfl⟩ := h.symm ▸ hβ
    refine ⟨⟨toRat α, toRat_mem_ratSpan (hJ' hα)⟩, ⟨α, hα, rfl⟩, ?_⟩
    exact Subtype.ext hβx

/-- Evaluate the shared all-test standard-Levi conjugation assertion on
rational points, preserving the actual ambient conjugating element. -/
theorem levi_map_conj_of_character_image
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (J J' : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (h : weylAction i n '' rootSet i ν J' = rootSet i ν J) :
    (levi i ν J').map (MulAut.conj (n : RationalPoint k G.X) : _ →* _) =
      levi i ν J := by
  have hencoded := relativeRootSubset_image_of_character_image i
    ((rootSet_subset i ν J').trans ((simpleRelativeRoots_subset_positive i ν).trans
      (positiveRelativeRoots_subset_relativeRoots i ν))) n h
  have hL := (hConj k G hG T i hi ν hν).1
    (rootSet i ν J) (rootSet i ν J')
    (rootSet_subset i ν J) (rootSet_subset i ν J') n hencoded
  have hmem (x : RationalPoint k G.X) :
      x ∈ levi i ν J' ↔
        (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈ levi i ν J := by
    change x ∈ (standardLevi i ν (rootSet i ν J')).carrier _ ↔ _
    rw [hL, SubgroupFunctor.mem_comap, comp_innerIso_hom, constantPoint_self]
  ext x
  change x ∈ (levi i ν J').map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom ↔
    x ∈ levi i ν J
  rw [Subgroup.mem_map_equiv]
  simpa [MulAut.conj_symm_apply, mul_assoc] using
    hmem ((n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X))

variable [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]

/-- The associated subset determined by the actual Coxeter longest element
has the required actual Levi image for every normalizer lift. -/
theorem associatedLeviConjugation_of_standard
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) CM)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs) :
    actualAssociatedLeviConjugation (torusPoints i) (levi i ν) cs := by
  intro J n hn
  have himage :
      weylCharacterAction i hN hZ (longestRep cs J) ''
          rootSet i ν (associatedSubset cs J) = rootSet i ν J := by
    rw [rootSet_associatedSubset i ν hN hZ cs hLength hSimple hMin hAssoc,
      Set.image_image]
    have hcancel :
        (fun α => weylCharacterAction i hN hZ (longestRep cs J)
          (weylCharacterAction i hN hZ (longestRep cs J)⁻¹ α)) = id := by
      funext α
      change (weylCharacterAction i hN hZ (longestRep cs J) *
        weylCharacterAction i hN hZ (longestRep cs J)⁻¹) α = α
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hcancel, Set.image_id]
  have hchar :
      weylAction i ((normalizerEquiv i hN).symm n) ''
          rootSet i ν (associatedSubset cs J) = rootSet i ν J := by
    rw [← weylCharacterAction_point_mk i hN hZ, hn]
    exact himage
  exact levi_map_conj_of_character_image i ν hG hi hν hConj
    J (associatedSubset cs J) ((normalizerEquiv i hN).symm n) hchar

/-- The actual inverse-conjugation equivalence used for representation
pullback from the associated Levi to the target Levi. -/
def associatedLeviConjugationEquiv
    [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) CM)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
    (J : Finset (SimpleRoot i ν)) (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    levi i ν J ≃ₜ* levi i ν (associatedSubset cs J) :=
  conjugationEquiv (n : RationalPoint k G.X)
    (conjugationMembership_of_map_eq _
      (associatedLeviConjugation_of_standard i ν hG hi hν hConj
        hN hZ cs hLength hSimple hMin hAssoc J n hn))

end Langlands.Aubert.General.RationalPointFamily
