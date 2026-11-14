import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamily

/-! # Exact normalizer criterion for actual conjugate families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S} {M T : Over S}

/-- A refinement of a parameter scheme gives the same underlying original test. -/
def familyRefinementTestIso (a : T ⟶ M) :
    T ≅ (Over.map M.hom).obj (Over.mk a.left) :=
  Over.isoMk (Iso.refl _) (by
    simpa only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom, Over.mk_hom]
      using Over.w a)

/-- Actual group points over a relative refinement are the original group points
on its underlying test scheme. -/
def familyRefinementPointsEquiv (a : T ⟶ M) :
    (Over.mk a.left ⟶ ((GroupScheme.baseChange M.hom).obj G).X) ≃* (T ⟶ G.X) :=
  (baseChangePointsEquiv M.hom G (Over.mk a.left)).trans
    (G.points.mapIso (familyRefinementTestIso a).op).groupIsoToMulEquiv

/-- The refinement point equivalence is projection followed by the canonical
identity-underlying comparison of tests. -/
theorem familyRefinementPointsEquiv_apply (a : T ⟶ M)
    (y : Over.mk a.left ⟶ ((GroupScheme.baseChange M.hom).obj G).X) :
    familyRefinementPointsEquiv (G := G) a y =
      (familyRefinementTestIso a).hom ≫ baseChangePointsEquiv M.hom G _ y := rfl

/-- Membership in a conjugate family may be tested on any original refinement. -/
theorem mem_range_conjugateFamily_refinement_iff (i : H ⟶ G) (g : M ⟶ G.X)
    (a : T ⟶ M) (x : T ⟶ G.X) :
    (familyRefinementPointsEquiv (G := G) a).symm x ∈
        (range (conjugateFamily i g)).carrier (Over.mk a.left) ↔
      (a ≫ g)⁻¹ * x * (a ≫ g) ∈ (range i).carrier T := by
  let w := familyRefinementTestIso a
  have transport (z : (Over.map M.hom).obj (Over.mk a.left) ⟶ G.X) :
      z ∈ (range i).carrier _ ↔ w.hom ≫ z ∈ (range i).carrier T :=
    ⟨fun hz => (range i).comp_mem w.hom hz, fun hz => by
      simpa only [Iso.inv_hom_id_assoc] using (range i).comp_mem w.inv hz⟩
  have hp : w.hom ≫ familyTestMap M (Over.mk a.left) ≫ g = a ≫ g := by
    apply Over.OverMorphism.ext
    simp only [w, familyRefinementTestIso, Over.isoMk_hom_left, Iso.refl_hom,
      Over.comp_left, familyTestMap, Over.homMk_left, Over.mk_hom, Category.id_comp]
  rw [mem_range_conjugateFamily_iff, transport]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, hp]
  change (a ≫ g)⁻¹ *
    familyRefinementPointsEquiv (G := G) a
      ((familyRefinementPointsEquiv (G := G) a).symm x) * (a ≫ g) ∈ _ ↔ _
  rw [MulEquiv.apply_symm_apply]

/-- Equality of actual conjugate families forces the quotient of their parameters
into the full normalizer, including every refinement and both directions. -/
theorem normalizer_of_range_conjugateFamily_eq (i : H ⟶ G)
    (g₁ g₂ : M ⟶ G.X)
    (heq : range (conjugateFamily i g₁) = range (conjugateFamily i g₂)) :
    g₁⁻¹ * g₂ ∈ (range i).normalizer.carrier M := by
  intro V a x hx
  have hc (z : V ⟶ G.X) :
      (a ≫ g₁)⁻¹ * z * (a ≫ g₁) ∈ (range i).carrier V ↔
        (a ≫ g₂)⁻¹ * z * (a ≫ g₂) ∈ (range i).carrier V := by
    have h₁ := mem_range_conjugateFamily_refinement_iff i g₁ a z
    have h₂ := mem_range_conjugateFamily_refinement_iff i g₂ a z
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  rw [MonObj.comp_mul, GrpObj.comp_inv]
  constructor
  · have hz : (a ≫ g₂)⁻¹ * ((a ≫ g₂) * x * (a ≫ g₂)⁻¹) *
        (a ≫ g₂) ∈ (range i).carrier V := by simpa [mul_assoc] using hx
    have hh := (hc ((a ≫ g₂) * x * (a ≫ g₂)⁻¹)).mpr hz
    convert hh using 1; group
  · have hz : (a ≫ g₁)⁻¹ * ((a ≫ g₁) * x * (a ≫ g₁)⁻¹) *
        (a ≫ g₁) ∈ (range i).carrier V := by simpa [mul_assoc] using hx
    have hh := (hc ((a ≫ g₁) * x * (a ≫ g₁)⁻¹)).mp hz
    convert hh using 1; group

/-- Exact all-test equality of conjugate families is full-normalizer coset equality. -/
theorem range_conjugateFamily_eq_iff (i : H ⟶ G) (g₁ g₂ : M ⟶ G.X) :
    range (conjugateFamily i g₁) = range (conjugateFamily i g₂) ↔
      g₁⁻¹ * g₂ ∈ (range i).normalizer.carrier M :=
  ⟨normalizer_of_range_conjugateFamily_eq i g₁ g₂,
    range_conjugateFamily_eq_of_normalizer i g₁ g₂⟩

end Langlands.GroupScheme.SubgroupFunctor
