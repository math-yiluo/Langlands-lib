import Langlands.Algebra.NondegenerateModuleAbelianStatements
import Langlands.Algebra.NondegenerateModuleClosureProof
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# Abelianness of the actual nondegenerate original-module category

Mathlib constructs abelian data from the four published closure properties,
retaining the inherited pointwise Hom groups on the actual full subcategory.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

namespace NondegenerateModuleCat

/-- Abelian data on the existing nondegenerate full subcategory. -/
@[instance_reducible] noncomputable def abelian (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    Abelian (NondegenerateModuleCat.{uA, uM} A) := by
  let h := nondegenerateModuleClosureStatement.{uA, uM} A hA
  let := h.1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2
  infer_instance

/-- The construction retains exactly the inherited original Hom groups. -/
theorem abelian_toPreadditive (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (abelian.{uA, uM} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} A) := rfl

end NondegenerateModuleCat

/-- The exact closed abelianness statement with no extra hypotheses. -/
theorem nondegenerateModuleAbelianStatement :
    NondegenerateModuleAbelianStatement.{uA, uM} := by
  intro A _ hA
  exact ⟨NondegenerateModuleCat.abelian A hA,
    NondegenerateModuleCat.abelian_toPreadditive A hA⟩

/-! Complete interfaces at arbitrary and both unequal universe pairs. -/

example : (A : Type uA) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Abelian (NondegenerateModuleCat.{uA, uM} A) :=
  @NondegenerateModuleCat.abelian.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (NondegenerateModuleCat.abelian.{uA, uM} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} A) :=
  @NondegenerateModuleCat.abelian_toPreadditive.{uA, uM}

example : NondegenerateModuleAbelianStatement.{uA, uM} :=
  @nondegenerateModuleAbelianStatement.{uA, uM}

example : NondegenerateModuleAbelianStatement.{0, 1} :=
  nondegenerateModuleAbelianStatement.{0, 1}

example : NondegenerateModuleAbelianStatement.{1, 0} :=
  nondegenerateModuleAbelianStatement.{1, 0}

example : (A : Type) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Abelian (NondegenerateModuleCat.{0, 1} A) :=
  @NondegenerateModuleCat.abelian.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Abelian (NondegenerateModuleCat.{1, 0} A) :=
  @NondegenerateModuleCat.abelian.{1, 0}

example : (A : Type) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (NondegenerateModuleCat.abelian.{0, 1} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{0, 1} A) :=
  @NondegenerateModuleCat.abelian_toPreadditive.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (NondegenerateModuleCat.abelian.{1, 0} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{1, 0} A) :=
  @NondegenerateModuleCat.abelian_toPreadditive.{1, 0}

end Langlands.Algebra
