import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SubgroupFunctor

/-! # Fixedness of the identity coset and subgroup containment -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G K : GroupScheme S} {Q : Over S}

/-- The section of a scheme quotient obtained from the identity of the group. -/
abbrev quotientIdentityPoint (q : G.X ⟶ Q) : Over.mk (𝟙 S) ⟶ Q :=
  HomogeneousQuotient.identityCoset G q

/-- The identity coset remains the identity coset on every scheme test. -/
@[simp]
theorem comp_quotientIdentityPoint (q : G.X ⟶ Q) {Z : Over S}
    (b : Z ⟶ Over.mk (𝟙 S)) :
    b ≫ quotientIdentityPoint q = (1 : Z ⟶ G.X) ≫ q := by
  rw [quotientIdentityPoint, HomogeneousQuotient.identityCoset,
    ← Category.assoc, MonObj.comp_one]

namespace SchemeAction

variable (a : SchemeAction G Q) (i : K ⟶ G)
variable (H : SubgroupFunctor G) (q : G.X ⟶ Q)
variable (hfib : ∀ (Z : Over S) (g h : Z ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier Z)
variable (hact : ∀ (Z : Over S) (g h : Z ⟶ G.X),
  a.act g (h ≫ q) = (g * h) ≫ q)

include hfib hact

/-- A subgroup fixes the identity coset on all tests exactly when its range
lies in the subgroup defining the quotient. -/
theorem isFixed_quotientIdentityPoint_iff :
    (a.restrict i).IsFixed (quotientIdentityPoint q) ↔
      SubgroupFunctor.range i ≤ H := by
  constructor
  · intro hfixed Z x hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have he := hfixed Z (toUnit Z) h
    rw [restrict_act, comp_quotientIdentityPoint, hact, mul_one] at he
    have hm := (hfib Z 1 (h ≫ i.hom.hom)).mp he.symm
    simpa only [inv_one, one_mul] using hm
  · intro hi Z b h
    rw [restrict_act, comp_quotientIdentityPoint, hact, mul_one]
    apply ((hfib Z 1 (h ≫ i.hom.hom)).mpr ?_).symm
    simpa only [inv_one, one_mul] using
      hi Z (show h ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier Z from ⟨h, rfl⟩)

end SchemeAction

end Langlands.GroupScheme
