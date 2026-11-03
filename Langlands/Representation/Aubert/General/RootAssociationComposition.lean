import Langlands.Representation.Aubert.General.RootAssociationLaws

/-! # Inverses and products of actual root-association representatives -/

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

/-- The inverse actual normalizer representative reverses root association. -/
theorem rootAssociation_inv {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hIJ : rootAssociation i ν hN hZ I J n) :
    rootAssociation i ν hN hZ J I n⁻¹ := by
  obtain ⟨hn, hIJ⟩ := hIJ
  let a : Group.RelativeWeyl.normalizer (torusPoints i) := ⟨n, hn⟩
  change weylCharacterAction i hN hZ (QuotientGroup.mk a) ''
    rootSet i ν I = rootSet i ν J at hIJ
  refine ⟨(Group.RelativeWeyl.normalizer (torusPoints i)).inv_mem hn, ?_⟩
  change weylCharacterAction i hN hZ (QuotientGroup.mk a⁻¹) ''
    rootSet i ν J = rootSet i ν I
  rw [QuotientGroup.mk_inv, map_inv, ← hIJ]
  ext α
  simp

/-- Successive root associations are represented by the product in the same
order as successive conjugations: first `n`, then `m`, gives `m * n`. -/
theorem rootAssociation_mul {I J K : Finset (SimpleRoot i ν)}
    {n m : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n)
    (hJK : rootAssociation i ν hN hZ J K m) :
    rootAssociation i ν hN hZ I K (m * n) := by
  obtain ⟨hn, hIJ⟩ := hIJ
  obtain ⟨hm, hJK⟩ := hJK
  let a : Group.RelativeWeyl.normalizer (torusPoints i) := ⟨n, hn⟩
  let b : Group.RelativeWeyl.normalizer (torusPoints i) := ⟨m, hm⟩
  change weylCharacterAction i hN hZ (QuotientGroup.mk a) ''
    rootSet i ν I = rootSet i ν J at hIJ
  change weylCharacterAction i hN hZ (QuotientGroup.mk b) ''
    rootSet i ν J = rootSet i ν K at hJK
  refine ⟨(Group.RelativeWeyl.normalizer (torusPoints i)).mul_mem hm hn, ?_⟩
  change weylCharacterAction i hN hZ (QuotientGroup.mk (b * a)) ''
    rootSet i ν I = rootSet i ν K
  rw [QuotientGroup.mk_mul, map_mul]
  change (weylCharacterAction i hN hZ (QuotientGroup.mk b) ∘
    weylCharacterAction i hN hZ (QuotientGroup.mk a)) '' rootSet i ν I = _
  simp only [Function.comp_def]
  rw [← Set.image_image
    (weylCharacterAction i hN hZ (QuotientGroup.mk b))
    (weylCharacterAction i hN hZ (QuotientGroup.mk a))
    (rootSet i ν I), hIJ, hJK]

/-- Reversing the direction and inverting the actual representative are
equivalent operations on root association. -/
theorem rootAssociation_inv_iff {I J : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} :
    rootAssociation i ν hN hZ J I n⁻¹ ↔ rootAssociation i ν hN hZ I J n := by
  constructor
  · intro h
    simpa only [inv_inv] using rootAssociation_inv i ν hN hZ h
  · exact rootAssociation_inv i ν hN hZ

/-- Inversion is an equivalence between the actual representatives of an
association and the representatives of its reverse. -/
def rootAssociationRepresentativesInvEquiv (I J : Finset (SimpleRoot i ν)) :
    {n : RationalPoint k G.X // rootAssociation i ν hN hZ I J n} ≃
      {n : RationalPoint k G.X // rootAssociation i ν hN hZ J I n} where
  toFun n := ⟨n.val⁻¹, rootAssociation_inv i ν hN hZ n.property⟩
  invFun n := ⟨n.val⁻¹, rootAssociation_inv i ν hN hZ n.property⟩
  left_inv n := Subtype.ext (inv_inv n.val)
  right_inv n := Subtype.ext (inv_inv n.val)

end Langlands.Aubert.General.RationalPointFamily
