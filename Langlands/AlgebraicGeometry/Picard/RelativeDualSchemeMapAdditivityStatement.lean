import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityStatement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Additivity of actual dual maps over a quasi-separated base -/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AbelianScheme

open Langlands.Scheme.Modules

/-- The addition equation for two fixed actual dual parameter schemes.
This predicate makes sense over every base. -/
def DualSchemeMapAdditivity
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    {S : Scheme.{u}} (A B : AbelianScheme S)
    (hA : HasDualScheme A) (hB : HasDualScheme B) : Prop :=
  ∀ f g : A ⟶ B,
    dualSchemeMap homPicardZeroPullback (f + g) hA hB =
      prod.lift (dualSchemeMap homPicardZeroPullback f hA hB)
        (dualSchemeMap homPicardZeroPullback g hA hB) ≫
          dualTensor stability A hA preservation

/-- Relative dualization preserves addition of input homomorphisms.
The quasi-separatedness hypothesis retains the convention of the source. -/
def RelativeDualSchemeMapAdditivityStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S]
    (A B : AbelianScheme S) (hA : HasDualScheme A) (hB : HasDualScheme B),
    DualSchemeMapAdditivity preservation stability A B hA hB

/-- The relative target implies the published field target. -/
lemma RelativeDualSchemeMapAdditivityStatement.field
    (additivity : RelativeDualSchemeMapAdditivityStatement.{u}) :
    FieldDualSchemeMapAdditivityStatement.{u} := by
  intro preservation stability k _ A B hA hB
  exact additivity preservation stability _ A B hA hB

end Langlands.AbelianScheme
