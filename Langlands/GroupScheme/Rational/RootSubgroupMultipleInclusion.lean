import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-! # Inclusion of positive-multiple root subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}
  (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- A character followed by the power homomorphism is its additive multiple. -/
theorem character_comp_powerHom (n : ℕ) :
    a ≫ Gm.powerHom B (n : ℤ) = n • a := by
  apply CommGroupScheme.hom_ext_points
  intro V x
  rw [comp_groupHom_comp, Gm.powerHom_apply, Gm.comp_zsmul_id]
  rw [← natCast_zsmul, comp_groupHom_zsmul]

/-- An extension through `n*a` gives one through `a` by the affine monomial
`t ↦ t^n`. Positivity is needed only for its value at zero. -/
theorem IsOrbitExtension.of_nsmul {n : ℕ} {T : Over B} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme B ⟶ G.X}
    (he : IsOrbitExtension i (n • a) g e) :
    IsOrbitExtension i a g (T ◁ AffineLine.powerMap B n ≫ e) := by
  rw [IsOrbitExtension]
  calc
    T ◁ ((CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion B) ≫
        (T ◁ AffineLine.powerMap B n ≫ e) =
      T ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
        (AffineLine.unitInclusion B ≫ AffineLine.powerMap B n)) ≫ e := by
          rw [← Category.assoc, ← whiskerLeft_comp, Category.assoc]
    _ = T ◁ ((CommGroupScheme.groupHom (n • a)).hom.hom ≫
        AffineLine.unitInclusion B) ≫ e := by
          rw [AffineLine.unitInclusion_comp_powerMap]
          rw [← character_comp_powerHom a n]
          rfl
    _ = orbit i g := he

/-- Positive multiples give smaller actual orbit-extension subgroup functors,
over an arbitrary base scheme and on every test scheme. -/
theorem subgroup_nsmul_le {n : ℕ} (hn : 0 < n) :
    subgroup i (n • a) ≤ subgroup i a := by
  intro T g hg
  obtain ⟨e, he, he0⟩ := hg
  exact ⟨T ◁ AffineLine.powerMap B n ≫ e, he.of_nsmul i a,
    (AffineLine.evalZero_whiskerLeft_powerMap B hn e).trans he0⟩

/-- In particular, the doubled-root subgroup is contained in the original one,
without a root-system, realization or cyclic-comparison hypothesis. -/
theorem double_subgroup_le :
    subgroup i (2 • a) ≤ subgroup i a :=
  subgroup_nsmul_le i a (by decide : 0 < (2 : ℕ))

/-- The full arbitrary-base inclusion for every positive natural multiple. -/
def RootSubgroupMultipleInclusionStatement : Prop :=
  ∀ (B : Scheme.{u}) (S : CommGroupScheme B) (G : GroupScheme B)
    (i : S.toGrp ⟶ G) (a : characterLattice S) (n : ℕ),
      0 < n → subgroup i (n • a) ≤ subgroup i a

/-- The intrinsic orbit-extension construction satisfies positive-multiple inclusion. -/
theorem rootSubgroupMultipleInclusion : RootSubgroupMultipleInclusionStatement.{u} :=
  fun _ _ _ i a _ hn => subgroup_nsmul_le i a hn

end Langlands.GroupScheme.RelativeRoot
