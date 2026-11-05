import Langlands.GroupScheme.Rational.PointedPowerFamily
import Langlands.GroupScheme.Rational.VectorFactorPointedFamilies
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionStatement
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # The characteristic-p criterion from explicit structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace UnipotentWoundCriterionReduction

variable {B : Scheme.{u}} {L U V W G : GroupScheme B}

/-- Send a line into a subgroup through its first product factor. -/
def lineThroughVectorFactor (j : L ⟶ V) (e : U ≅ V ⊗ W) (w : U ⟶ G) :
    L ⟶ G :=
  (j ≫ VectorFactorPointedFamilies.leftInclusion V W ≫ e.inv) ≫ w

/-- A closed line remains closed through the product and subgroup inclusions. -/
theorem isClosedSubgroup_lineThroughVectorFactor [IsSeparated W.X.hom]
    (j : L ⟶ V) (hj : IsClosedSubgroup j) (e : U ≅ V ⊗ W)
    (w : U ⟶ G) (hw : IsClosedSubgroup w) :
    IsClosedSubgroup (lineThroughVectorFactor j e w) :=
  (hj.comp ((VectorFactorPointedFamilies.isClosedSubgroup_leftInclusion V W).comp_iso
    e.symm)).comp hw

/-- A line in a central subgroup is central in the ambient group. -/
theorem isCentral_lineThroughVectorFactor
    (j : L ⟶ V) (e : U ≅ V ⊗ W) (w : U ⟶ G) (hw : IsCentral w) :
    IsCentral (lineThroughVectorFactor j e w) :=
  hw.comp _

section Field

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A nonconstant affine-line map supplies an actual central closed additive
line, conditional on the rational-point and commutative p-torsion factor results. -/
theorem exists_central_additive_closed_subgroup_of_charP
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u})
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension L 1 := by
  obtain ⟨n, U, w, f, hw, hUs, hUa, _hUgc, hUc, hwc, ht, hf, h₀⟩ :=
    exists_pointed_torsion_central_family_of_not_hasConstantAffineLineMaps p hU hG
  obtain ⟨V, W, ⟨e⟩, ⟨d, hV⟩, _hWs, hWa, _hWc, _hWU, hW⟩ :=
    hFactor k p U hUs hUa hUc ht
  let : IsAffineHom W.X.hom := hWa
  have hd : 0 < d :=
    VectorFactorPointedFamilies.vector_dimension_pos hP e hV hW n f hf h₀
  obtain ⟨L, j, hj, hL⟩ := VectorFactorPointedFamilies.exists_closed_vectorLine hV hd
  exact ⟨L, lineThroughVectorFactor j e w,
    isClosedSubgroup_lineThroughVectorFactor j hj e w hw,
    isCentral_lineThroughVectorFactor j e w hwc, hL⟩

/-- The characteristic-p equivalence with the two structural inputs explicit. -/
theorem criterion_of_charP
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u})
    (p : ℕ) [Fact p.Prime] [CharP k p] (hU : IsUnipotent G) :
    HasConstantAffineLineMaps G ↔
      ¬ ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
        IsClosedSubgroup j ∧ IsCentral j ∧
          RelativeRoot.IsVectorGroupOfDimension L 1 := by
  refine ⟨HasConstantAffineLineMaps.not_exists_central_additive_closed_subgroup, ?_⟩
  intro h
  by_contra hG
  exact h (exists_central_additive_closed_subgroup_of_charP hP hFactor p hU hG)

end Field

end UnipotentWoundCriterionReduction

end Langlands.GroupScheme
