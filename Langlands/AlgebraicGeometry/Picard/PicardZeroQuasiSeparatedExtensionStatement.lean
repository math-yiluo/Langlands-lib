import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBundle
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Extending Picard-zero classification from quasi-separated tests -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The existing actual Picard-zero universal property restricted to
quasi-separated test schemes. The parameter scheme is unrestricted. -/
def IsUniversalPicardZeroOnQuasiSeparatedTests {P : Over S}
    (L : RigidifiedFamily A P) : Prop :=
  IsPicardZeroFamily A L ∧
    ∀ (T : Over S) [QuasiSeparatedSpace T.left] (q : PicardZeroClasses A T),
      ∃! h : T ⟶ P,
        RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
          (unitSection_comp A) L T h = q.val

/-- A supplied actual Picard-zero family universal on quasi-separated tests
over a quasi-separated base is universal on every test scheme. -/
def PicardZeroQuasiSeparatedExtensionStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (P : Over S) (L : RigidifiedFamily A P),
    IsUniversalPicardZeroOnQuasiSeparatedTests A L → IsUniversalPicardZero A L

end Langlands.AbelianScheme
