import Langlands.GroupScheme.Rational.AffineLineRigidity
import Langlands.GroupScheme.Rational.RootSubgroupNontrivial

/-! # Central additive-subgroup criterion for affine-line constancy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The all-field analogue of conditions (1) and (2) in CGP Proposition B.3.2,
expressed using actual central closed subgroups and natural vector coordinates.
This is a proposition target, not a proof of the equivalence. -/
def UnipotentWoundCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    IsUnipotent G →
      (HasConstantAffineLineMaps G ↔
        ¬ ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
          IsClosedSubgroup j ∧ IsCentral j ∧
            RelativeRoot.IsVectorGroupOfDimension V 1)

namespace HasConstantAffineLineMaps

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Affine-line constancy excludes any one-dimensional vector closed subgroup.
This implication needs neither centrality nor geometric assumptions on `G`. -/
theorem not_isVectorGroupOfDimension_one_closed_subgroup
    (hG : HasConstantAffineLineMaps G)
    {V : GroupScheme (Spec (CommRingCat.of k))} (j : V ⟶ G)
    (hj : IsClosedSubgroup j) (hV : RelativeRoot.IsVectorGroupOfDimension V 1) :
    False := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hj0 := hG.hom_eq_zero_of_isVectorGroupOfDimension_one hV j
  obtain ⟨x, hx⟩ := hV.exists_rationalPoint_ne_one (by decide)
  apply hx
  apply (cancel_mono j.hom.hom).mp
  calc
    x ≫ j.hom.hom = 1 := by
      rw [hj0]
      exact MonObj.comp_one _
    _ = 1 ≫ j.hom.hom := (MonObj.one_comp _).symm

/-- The forward direction of the central additive-subgroup criterion is
already unconditional for every actual group scheme. -/
theorem not_exists_central_additive_closed_subgroup
    (hG : HasConstantAffineLineMaps G) :
    ¬ ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
      IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension V 1 := by
  rintro ⟨V, j, hj, _, hV⟩
  exact hG.not_isVectorGroupOfDimension_one_closed_subgroup j hj hV

end HasConstantAffineLineMaps

end Langlands.GroupScheme
