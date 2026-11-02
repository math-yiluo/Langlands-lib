import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The Euler characteristic of an inverse line bundle on an abelian variety -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- On a `g`-dimensional abelian scheme over an algebraically closed field, if the tensor
product of two line bundles `N` and `M` is trivial, so that `M` is an inverse of `N`, then
`χ(M) = (-1)^g χ(N)` (Edixhoven, van der Geer and Moonen, *Abelian Varieties*, (9.11) and
formula (7) with `m = -1`).
This proposition is a statement target, not a proof. -/
def AlgClosedFieldEulerInverseSymmetryStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (N M : LineBundle A.X.left),
        Nonempty (tensorObj N.obj M.obj ≅ structureSheaf A.X.left) →
          ∀ (hN : HasFiniteCohomology A.X.hom N.obj)
            (hM : HasFiniteCohomology A.X.hom M.obj),
            eulerCharacteristic A.X.hom M.obj hM =
              (-1) ^ g * eulerCharacteristic A.X.hom N.obj hN

end Langlands.AbelianScheme
