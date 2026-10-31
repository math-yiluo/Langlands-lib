import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Abelianness with the inherited original Hom groups

Renard I.1.2 asserts abelianness of the nondegenerate full subcategory.
This proposition requires the actual structure to extend the pointwise
preadditive structure inherited from the published ambient category.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

/-- The actual nondegenerate category is abelian with its inherited Hom groups. -/
def NondegenerateModuleAbelianStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
    ∃ h : Abelian (NondegenerateModuleCat.{uA, uM} A),
      h.toPreadditive = Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} A)

/-! Complete closed interfaces, including both unequal-universe cases. -/

example : Prop := NondegenerateModuleAbelianStatement.{uA, uM}

example : NondegenerateModuleAbelianStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
      ∃ h : Abelian (NondegenerateModuleCat.{uA, uM} A),
        h.toPreadditive =
          Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} A)) := rfl

example : NondegenerateModuleAbelianStatement.{0, 1} =
    (∀ (A : Type) [NonUnitalRing A], IsIdempotented A →
      ∃ h : Abelian (NondegenerateModuleCat.{0, 1} A),
        h.toPreadditive =
          Preadditive.fullSubcategory (nondegenerateProperty.{0, 1} A)) := rfl

example : NondegenerateModuleAbelianStatement.{1, 0} =
    (∀ (A : Type 1) [NonUnitalRing A], IsIdempotented A →
      ∃ h : Abelian (NondegenerateModuleCat.{1, 0} A),
        h.toPreadditive =
          Preadditive.fullSubcategory (nondegenerateProperty.{1, 0} A)) := rfl

end Langlands.Algebra
