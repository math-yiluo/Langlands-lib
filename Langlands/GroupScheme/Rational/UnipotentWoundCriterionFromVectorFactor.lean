import Langlands.GroupScheme.Rational.SmoothPointedFamilyRigidity
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionCharPReduction
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionCharZero

/-! # The central criterion from the sole remaining vector-factor input -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentWoundCriterionReduction

section CharP

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The vector-factor theorem alone supplies a central closed additive line
from a nonconstant affine-line map in prime characteristic. -/
theorem exists_central_additive_closed_subgroup_of_charP_of_vectorFactor
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
    VectorFactorPointedFamilies.vector_dimension_pos_of_smooth e hV hW n f hf h₀
  obtain ⟨L, j, hj, hL⟩ := VectorFactorPointedFamilies.exists_closed_vectorLine hV hd
  exact ⟨L, lineThroughVectorFactor j e w,
    isClosedSubgroup_lineThroughVectorFactor j hj e w hw,
    isCentral_lineThroughVectorFactor j e w hwc, hL⟩

/-- The prime-characteristic criterion retains only the vector-factor input. -/
theorem criterion_of_charP_of_vectorFactor
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u})
    (p : ℕ) [Fact p.Prime] [CharP k p] (hU : IsUnipotent G) :
    HasConstantAffineLineMaps G ↔
      ¬ ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
        IsClosedSubgroup j ∧ IsCentral j ∧
          RelativeRoot.IsVectorGroupOfDimension L 1 := by
  refine ⟨HasConstantAffineLineMaps.not_exists_central_additive_closed_subgroup, ?_⟩
  intro h
  by_contra hG
  exact h (exists_central_additive_closed_subgroup_of_charP_of_vectorFactor hFactor p hU hG)

end CharP

/-- The unchanged exact all-field criterion follows from the vector-factor
proposition alone. -/
theorem criterion_of_vectorFactor
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u}) :
    UnipotentWoundCriterionStatement.{u} := by
  intro k _ G hs ha hc hU
  let : Smooth G.X.hom := hs
  let : IsAffineHom G.X.hom := ha
  let : ConnectedSpace G.X.left := hc
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let : CharZero k := hzero
    exact criterion_of_charZero hU
  · let : Fact p.Prime := hp
    let : CharP k p := hchar
    exact criterion_of_charP_of_vectorFactor hFactor p hU

/-- Choose an actual central closed additive line under the sole remaining
vector-factor input. -/
def centralAdditiveLineOfVectorFactor
    (hFactor : RelativeRoot.CommutativePTorsionVectorFactorStatement.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    Σ L : GroupScheme (Spec (CommRingCat.of k)),
      {j : L ⟶ G // IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension L 1} :=
  Classical.choice (by
    have h := (criterion_of_vectorFactor hFactor k G
      inferInstance inferInstance inferInstance hU).not.mp hG
    obtain ⟨L, j, hj, hcent, hL⟩ := Classical.not_not.mp h
    exact ⟨⟨L, j, hj, hcent, hL⟩⟩)

end Langlands.GroupScheme.UnipotentWoundCriterionReduction
