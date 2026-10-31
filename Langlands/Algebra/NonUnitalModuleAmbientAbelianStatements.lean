import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Ambient abelianness of original additive nonunital modules

This statement requires actual Abelian data extending the published pointwise
preadditive structure. It supplies no Abelian instance or proof.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

/-- The original category is abelian with its published pointwise Hom groups. -/
def NonUnitalModuleAmbientAbelianStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    ∃ h : Abelian (NonUnitalModuleCat.{uA, uM} A),
      h.toPreadditive = NonUnitalModuleCat.preadditive.{uA, uM} A

end Langlands.Algebra
