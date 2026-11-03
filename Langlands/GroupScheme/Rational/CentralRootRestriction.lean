import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Restricting actual roots to a central split torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section GeneralBase

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom]
  {T A : CommGroupScheme (Spec R)}

/-- All-test centrality makes the actual adjoint action trivial. -/
theorem IsCentral.adjoint_eq (a : H ⟶ G) (ha : IsCentral a)
    {B : Type u} [CommRing B] [Algebra R B]
    (t : Lie.AffinePoints H B) (X : Additive (lieKernel G B)) :
    adjoint G B (t ≫ a.hom.hom) X = X := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [adjoint_val]
  have hc : Commute (Lie.constant G (t ≫ a.hom.hom)) X.toMul.val := by
    have h := (ha _ t) _
      ((algSpec R).map (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom R B B)).op) X.toMul.val
    simpa only [Lie.constant, Lie.affineMap_apply, Category.assoc] using h
  rw [hc.eq, mul_inv_cancel_right]

/-- Every Lie vector has weight zero for a central homomorphism. -/
theorem weightSpace_zero_eq_top_of_isCentral (a : A.toGrp ⟶ G) (ha : IsCentral a) :
    weightSpace a 0 = ⊤ := by
  apply top_unique
  intro X _ B _ _ t
  rw [ha.adjoint_eq a, Lie.characterValue_zero, Units.val_one, one_smul]

/-- Restriction along an actual torus homomorphism restricts every adjoint weight. -/
theorem weightSpace_le_restrict (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (χ : characterLattice T) :
    weightSpace i χ ≤ weightSpace (CommGroupScheme.groupHom f ≫ i) (f ≫ χ) := by
  intro X hX B _ _ t
  have h := (mem_weightSpace.mp hX) B (t ≫ (CommGroupScheme.groupHom f).hom.hom)
  change adjoint G B (t ≫ (CommGroupScheme.groupHom f).hom.hom ≫ i.hom.hom) _ =
    (Lie.characterValue (f ≫ χ) t : B) • _
  rw [Lie.characterValue_comp]
  simpa only [Category.assoc] using h

end GeneralBase

section Field

open Langlands.LinearAlgebra.RationalSpan

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every actual root restricts to zero along a central split torus. -/
theorem root_restrict_eq_zero_of_isCentral (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i))
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) : f ≫ χ = 0 := by
  classical
  by_contra hn
  have hd := (isInternal_weightSpace_of_isSplitTorus k G A hA
    (CommGroupScheme.groupHom f ≫ i)).submodule_iSupIndep.pairwiseDisjoint hn
  change Disjoint (weightSpace (CommGroupScheme.groupHom f ≫ i) (f ≫ χ))
    (weightSpace (CommGroupScheme.groupHom f ≫ i) 0) at hd
  rw [weightSpace_zero_eq_top_of_isCentral _ hc, disjoint_top] at hd
  apply (mem_relativeRoots.mp hχ).2
  exact le_antisymm ((weightSpace_le_restrict i f χ).trans hd.le) bot_le

/-- The rational span of all actual roots lies in the central restriction kernel. -/
theorem relativeRootSpan_le_centralRestrictionKer (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) :
    relativeRootSpan i ≤
      (rationalCharacterRestrictRat (CommGroupScheme.groupHom f)).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨χ, hχ, rfl⟩
  change rationalCharacterRestrictRat (CommGroupScheme.groupHom f) (toRat χ) = 0
  rw [rationalCharacterRestrictRat_toRat]
  change toRat (f ≫ χ) = 0
  rw [root_restrict_eq_zero_of_isCentral i f hA hc hχ, map_zero]

/-- The real span of all actual roots lies in the central restriction kernel. -/
theorem relativeRootSpanReal_le_centralRestrictionKer (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) :
    RealTorusSpace.relativeRootSpanReal i ≤
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨χ, hχ, rfl⟩
  change rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
    ((1 : ℝ) ⊗ₜ[ℤ] χ) = 0
  rw [rationalCharacterRestrictReal_tmul]
  change (1 : ℝ) ⊗ₜ[ℤ] (f ≫ χ) = 0
  rw [root_restrict_eq_zero_of_isCentral i f hA hc hχ, TensorProduct.tmul_zero]

/-- The actual rational root span embeds in the kernel of restriction to a central split torus. -/
def relativeRootSpanCentralRestrictionKer (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) :
    relativeRootSpan i →ₗ[ℚ]
      (rationalCharacterRestrictRat (CommGroupScheme.groupHom f)).ker :=
  Submodule.inclusion (relativeRootSpan_le_centralRestrictionKer i f hA hc)

@[simp]
theorem relativeRootSpanCentralRestrictionKer_coe (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (x : relativeRootSpan i) :
    (relativeRootSpanCentralRestrictionKer i f hA hc x :
      ℚ ⊗[ℤ] characterLattice T) = x := rfl

end Field

end Langlands.GroupScheme
