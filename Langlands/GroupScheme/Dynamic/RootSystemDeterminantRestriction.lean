import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Rational.RelativeReflectionProperties

/-! # Opposite weight spaces and determinant restrictions from the actual root system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

section Multiplicity

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The supplied actual root system gives a rational normalizer point negating
each actual relative root, without choosing integral coroot data. -/
theorem HasRelativeRootSystem.exists_normalizerPoint_weylAction_eq_neg
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    ∃ n : normalizerPoints i, weylAction i n α = -α := by
  obtain ⟨w, hw⟩ := hroot.exists_isRelativeReflection hα
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨n, hT.character_toRat_injective ?_⟩
  have h := congrArg Subtype.val hw.relativeWeylAction_apply_self
  change toRat (weylAction i n α) = -toRat α at h
  simpa only [map_neg] using h

omit [Mono i.hom.hom.left] in
private theorem normalizerAdjoint_injective (n : normalizerPoints i) :
    Function.Injective (basePointAdjoint (n : rationalPoints G)) := by
  intro X Y hXY
  have h := congrArg (basePointAdjoint (n : rationalPoints G)⁻¹) hXY
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, basePointAdjoint_inv_mul,
    Module.End.one_apply, Module.End.one_apply] at h

private def normalizerWeightSpaceEquiv (n : normalizerPoints i) (α : characterLattice T) :
    weightSpace i α ≃ₗ[k] weightSpace i (weylAction i n α) :=
  (Submodule.equivMapOfInjective _ (normalizerAdjoint_injective n)
    (weightSpace i α)).trans
      (LinearEquiv.ofEq _ _ (map_weightSpace_weylAction n α))

private theorem weightSpace_eq_neg_of_not_root
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ∉ relativeRoots i) :
    weightSpace i α = weightSpace i (-α) := by
  by_cases h0 : α = 0
  · simp only [h0, neg_zero]
  have hnα : -α ∉ relativeRoots i := by
    intro h
    exact hα (by simpa only [neg_neg] using hroot.neg_mem_relativeRoots i hT h)
  have hb : ∀ β : characterLattice T, β ∉ relativeRoots i → β ≠ 0 →
      weightSpace i β = ⊥ := by
    intro β hβ hβ0
    by_contra h
    exact hβ ⟨hβ0, h⟩
  rw [hb α hα h0, hb (-α) hnα (neg_ne_zero.mpr h0)]

/-- Equivalence between the actual opposite character weight spaces. For a
root it is adjoint transport by a chosen rational normalizer reflection; for
zero and nonroots it is transport along equality of the submodules. -/
def HasRelativeRootSystem.negWeightSpaceEquiv
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (α : characterLattice T) :
    weightSpace i α ≃ₗ[k] weightSpace i (-α) := by
  classical
  by_cases hα : α ∈ relativeRoots i
  · let n := (hroot.exists_normalizerPoint_weylAction_eq_neg hT hα).choose
    have hn : weylAction i n α = -α :=
      (hroot.exists_normalizerPoint_weylAction_eq_neg hT hα).choose_spec
    exact (normalizerWeightSpaceEquiv n α).trans
      (LinearEquiv.ofEq _ _ (congrArg (weightSpace i) hn))
  · exact LinearEquiv.ofEq _ _ (weightSpace_eq_neg_of_not_root hroot hT hα)

/-- Opposite weight multiplicities agree under the already supplied root-system
hypothesis; finite dimensionality is not needed for this consequence. -/
theorem HasRelativeRootSystem.finrank_weightSpace_neg
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (α : characterLattice T) :
    Module.finrank k (weightSpace i (-α)) = Module.finrank k (weightSpace i α) :=
  (hroot.negWeightSpaceEquiv hT α).finrank_eq.symm

/-- The positive-weight determinant sums for opposite cocharacters are
opposite, using the supplied root system rather than integral reflection data. -/
theorem HasRelativeRootSystem.positiveWeightCharacter_neg
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (ζ : cocharacterLattice T) :
    positiveWeightCharacter i (-ζ) = -positiveWeightCharacter i ζ := by
  unfold positiveWeightCharacter
  rw [← finsum_comp_equiv (Equiv.neg (characterLattice T)), ← finsum_neg_distrib]
  apply finsum_congr
  intro α
  simp only [Equiv.neg_apply, map_neg, LinearMap.neg_apply, neg_neg, smul_neg]
  rw [show (Equiv.neg (characterLattice T)) α = -α from rfl,
    hroot.finrank_weightSpace_neg hT]

end Multiplicity

section Determinants

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
  (ζ : cocharacterLattice T)
  {Z U V : GroupScheme (Spec (CommRingCat.of k))}
  {iZ : Z ⟶ G} {iU : U ⟶ G} {iV : V ⟶ G}
  (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iZ)
  (hZ' : (Dynamic.centralizer (CommGroupScheme.groupHom (-ζ) ≫ i)).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iU)
  (hV : (Dynamic.unipotent (CommGroupScheme.groupHom (-ζ) ≫ i)).IsRepresentedBy iV)
  [IsAffine Z.X.left] [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)
  {d e : ℕ} (c : Lie.FiniteCoordinates U d) (c' : Lie.FiniteCoordinates V e)

include hroot hT hj

/-- Opposite dynamic determinant characters sum to zero after restriction to
the actual split torus. This makes no claim of character detection on `Z`. -/
theorem characterRestrict_oppositeDeterminant_add_eq_zero_of_rootSystem :
    characterRestrict j
      ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c +
        (Dynamic.centralizerAdjointAction hZ' hV).determinantCharacter c') = 0 := by
  rw [map_add, characterRestrict_centralizerAdjointDeterminant hT i ζ hZ hU j hj c,
    characterRestrict_centralizerAdjointDeterminant hT i (-ζ) hZ' hV j hj c',
    hroot.positiveWeightCharacter_neg hT, add_neg_cancel]

/-- On points in the image of `T(k)`, the two actual determinant values multiply
to one, with the same represented models and finite Lie coordinates. -/
theorem rationalCharacterEval_oppositeDeterminant_mul_eq_one_of_rootSystem
    (t : rationalPoints T.toGrp) :
    rationalCharacterEval
        ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c)
        (rationalPoints.map j t) *
      rationalCharacterEval
        ((Dynamic.centralizerAdjointAction hZ' hV).determinantCharacter c')
        (rationalPoints.map j t) = 1 := by
  rw [← rationalCharacterEval_add, ← rationalCharacterEval_characterRestrict,
    characterRestrict_oppositeDeterminant_add_eq_zero_of_rootSystem
      hroot hT ζ hZ hZ' hU hV j hj c c',
    rationalCharacterEval_zero]

end Determinants

end Langlands.GroupScheme
