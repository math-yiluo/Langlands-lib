import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The `k^(2g)` scaling of the Euler product of an ample line bundle and its inverse -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- On a `g`-dimensional abelian scheme over an algebraically closed field, let `H` be an
ample line bundle with inverse `N`, let `k ≥ 1`, and let `Nk` be an inverse of the tensor
power `H^{⊗k}`. Then `χ(H^{⊗k}) · χ(Nk) = k^(2g) · χ(H) · χ(N)`. This is derived from
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, (9.11) and formula (7),
`χ(L^m) = m^g χ(L)`, applied with `m = k, -k, -1`.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldAmpleEulerInverseScalingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (H N : LineBundle A.X.left), H.IsAmple →
        Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left) →
          ∀ (k : ℕ), 1 ≤ k →
            ∀ (Nk : LineBundle A.X.left),
              Nonempty (tensorObj (tensorPow H.obj k) Nk.obj ≅ structureSheaf A.X.left) →
                ∀ (hH : HasFiniteCohomology A.X.hom H.obj)
                  (hN : HasFiniteCohomology A.X.hom N.obj)
                  (hHk : HasFiniteCohomology A.X.hom (tensorPow H.obj k))
                  (hNk : HasFiniteCohomology A.X.hom Nk.obj),
                  eulerCharacteristic A.X.hom (tensorPow H.obj k) hHk *
                      eulerCharacteristic A.X.hom Nk.obj hNk =
                    (k : ℤ) ^ (2 * g) *
                      (eulerCharacteristic A.X.hom H.obj hH *
                        eulerCharacteristic A.X.hom N.obj hN)

end Langlands.AbelianScheme
