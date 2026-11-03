import Langlands.GroupScheme.Rational.StandardLeviConjugationAssembly
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Representation.Aubert.General.RationalStandardComplex

/-! # Root association and the actual support-category conjugation witness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

include hG hi hν hStandard

/-- A root-association witness carries the source Levi to the target Levi
by conjugation with the very same rational point. -/
theorem levi_map_conj_of_rootAssociation
    (I J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X)
    (hA : rootAssociation i ν hN hZ I J n) :
    (levi i ν I).map (MulAut.conj n : _ →* _) = levi i ν J := by
  obtain ⟨hn, himage⟩ := hA
  have hchar :
      weylAction i ((normalizerEquiv i hN).symm ⟨n, hn⟩) '' rootSet i ν I =
        rootSet i ν J := by
    rw [← weylCharacterAction_point_mk i hN hZ]
    exact himage
  exact levi_map_conj_of_character_image i ν hG hi hν
    (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
    J I ((normalizerEquiv i hN).symm ⟨n, hn⟩) hchar

/-- The exact inverse-conjugation membership equivalence in the support
category follows from root association and the visible structural premise. -/
theorem conjugationMembership_of_rootAssociation
    (I J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X)
    (hA : rootAssociation i ν hN hZ I J n) :
    ∀ x : RationalPoint k G.X,
      x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I :=
  conjugationMembership_of_map_eq n
    (levi_map_conj_of_rootAssociation i ν hG hi hν hStandard hN hZ I J n hA)

/-- The corresponding continuous group equivalence is inverse conjugation
from the target standard Levi to the source standard Levi. -/
def rootAssociationLeviConjugationEquiv
    [TopologicalSpace (RationalPoint k G.X)]
    [IsTopologicalGroup (RationalPoint k G.X)]
    (I J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X)
    (hA : rootAssociation i ν hN hZ I J n) :
    levi i ν J ≃ₜ* levi i ν I :=
  conjugationEquiv n
    (conjugationMembership_of_rootAssociation i ν hG hi hν hStandard hN hZ I J n hA)

/-- Under the target's structural data, its quantified nonconjugacy condition
is equivalent to the absence of root-association witnesses for subsets of K. -/
theorem no_associated_levi_iff_no_rootAssociation
    (I K : Finset (SimpleRoot i ν)) :
    (∀ (J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X),
      J ⊆ K → rootAssociation i ν hN hZ I J n →
        ¬ ∀ x : RationalPoint k G.X,
          x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I) ↔
    ∀ (J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X),
      J ⊆ K → ¬ rootAssociation i ν hN hZ I J n := by
  constructor
  · intro h J n hJK hA
    exact h J n hJK hA
      (conjugationMembership_of_rootAssociation i ν hG hi hν hStandard hN hZ I J n hA)
  · intro h J n hJK hA
    exact (h J n hJK hA).elim

end Langlands.Aubert.General.RationalPointFamily
