import Langlands.Algebra.NonUnitalModuleAmbientAbelianStatements
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Ambient abelianness of original additive nonunital modules

Transfer abelianness through the published integer-unitization equivalence,
retaining the published pointwise preadditive structure and finite products.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

namespace NonUnitalModuleCat

/-- Abelian structure on the original category with independent universes. -/
noncomputable instance abelian (A : Type uA) [NonUnitalRing A] :
    Abelian (NonUnitalModuleCat.{uA, uM} A) :=
  abelianOfEquivalence (IntegerUnitization.extendFunctor.{uA, uM} A)

/-- Transfer retains exactly the published pointwise Hom groups. -/
theorem abelian_toPreadditive (A : Type uA) [NonUnitalRing A] :
    (abelian.{uA, uM} A).toPreadditive = preadditive.{uA, uM} A := rfl

end NonUnitalModuleCat

/-- The exact published closed proposition, with no additional inputs. -/
theorem nonUnitalModuleAmbientAbelianStatement :
    NonUnitalModuleAmbientAbelianStatement.{uA, uM} := by
  intro A _
  exact ⟨NonUnitalModuleCat.abelian A, NonUnitalModuleCat.abelian_toPreadditive A⟩

/-! Complete interfaces and both unequal-universe specializations. -/

example : (A : Type uA) → [NonUnitalRing A] →
    Abelian (NonUnitalModuleCat.{uA, uM} A) :=
  @NonUnitalModuleCat.abelian.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (NonUnitalModuleCat.abelian.{uA, uM} A).toPreadditive =
      NonUnitalModuleCat.preadditive.{uA, uM} A :=
  @NonUnitalModuleCat.abelian_toPreadditive.{uA, uM}

example : NonUnitalModuleAmbientAbelianStatement.{uA, uM} :=
  @nonUnitalModuleAmbientAbelianStatement.{uA, uM}

example : NonUnitalModuleAmbientAbelianStatement.{0, 1} :=
  nonUnitalModuleAmbientAbelianStatement.{0, 1}

example : NonUnitalModuleAmbientAbelianStatement.{1, 0} :=
  nonUnitalModuleAmbientAbelianStatement.{1, 0}

example : (A : Type) → [NonUnitalRing A] →
    Abelian (NonUnitalModuleCat.{0, 1} A) :=
  @NonUnitalModuleCat.abelian.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    Abelian (NonUnitalModuleCat.{1, 0} A) :=
  @NonUnitalModuleCat.abelian.{1, 0}

example : (A : Type) → [NonUnitalRing A] →
    (NonUnitalModuleCat.abelian.{0, 1} A).toPreadditive =
      NonUnitalModuleCat.preadditive.{0, 1} A :=
  @NonUnitalModuleCat.abelian_toPreadditive.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    (NonUnitalModuleCat.abelian.{1, 0} A).toPreadditive =
      NonUnitalModuleCat.preadditive.{1, 0} A :=
  @NonUnitalModuleCat.abelian_toPreadditive.{1, 0}

example (A : Type uA) [NonUnitalRing A] :
    Abelian (NonUnitalModuleCat.{uA, uM} A) := inferInstance

end Langlands.Algebra
