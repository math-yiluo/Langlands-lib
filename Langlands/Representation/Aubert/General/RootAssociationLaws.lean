import Langlands.Representation.Aubert.General.RationalStandardComplex

/-! # Elementary laws for the actual association of simple-root subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

private def rootSetSubtypeEquiv (I : Finset (SimpleRoot i ν)) :
    I ≃ rootSet i ν I :=
  Equiv.Set.image Subtype.val (I : Set (SimpleRoot i ν)) Subtype.val_injective

/-- An actual normalizer association gives an equivalence of the finite
sets of literal simple-root labels. -/
def rootAssociationEquiv {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hIJ : rootAssociation i ν hN hZ I J n) : I ≃ J := by
  let e := weylCharacterAction i hN hZ (QuotientGroup.mk ⟨n, Classical.choose hIJ⟩)
  exact (rootSetSubtypeEquiv i ν I).trans
    ((Equiv.Set.image e (rootSet i ν I) e.injective).trans
      ((Set.equivOfEq (Classical.choose_spec hIJ)).trans
        (rootSetSubtypeEquiv i ν J).symm))

/-- The literal identity representative associates every root subset to itself. -/
theorem rootAssociation_one (I : Finset (SimpleRoot i ν)) :
    rootAssociation i ν hN hZ I I 1 := by
  refine ⟨(Group.RelativeWeyl.normalizer (torusPoints i)).one_mem, ?_⟩
  change weylCharacterAction i hN hZ (QuotientGroup.mk
    (1 : Group.RelativeWeyl.normalizer (torusPoints i))) '' rootSet i ν I = _
  simp

/-- Association preserves the number of simple-root labels. -/
theorem rootAssociation_card_eq {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hIJ : rootAssociation i ν hN hZ I J n) :
    I.card = J.card := by
  simpa using Fintype.card_congr (rootAssociationEquiv i ν hN hZ hIJ)

/-- Only the empty subset can be associated to the empty subset. -/
theorem rootAssociation_empty_iff {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hIJ : rootAssociation i ν hN hZ I J n) :
    I = ∅ ↔ J = ∅ := by
  rw [← Finset.card_eq_zero, ← Finset.card_eq_zero,
    rootAssociation_card_eq i ν hN hZ hIJ]

variable [Fintype (SimpleRoot i ν)]

/-- Association preserves the full subset and hence properness. -/
theorem rootAssociation_univ_iff {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hIJ : rootAssociation i ν hN hZ I J n) :
    I = Finset.univ ↔ J = Finset.univ := by
  rw [← Finset.card_eq_iff_eq_univ, ← Finset.card_eq_iff_eq_univ,
    rootAssociation_card_eq i ν hN hZ hIJ]

/-- An associate of a proper standard subset is again proper. -/
theorem rootAssociation_ne_univ {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hIJ : rootAssociation i ν hN hZ I J n)
    (hI : I ≠ Finset.univ) : J ≠ Finset.univ :=
  fun hJ => hI ((rootAssociation_univ_iff i ν hN hZ hIJ).mpr hJ)

end Langlands.Aubert.General.RationalPointFamily
