import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Tensor-power and Euler dilation from an actual polarization -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- An actual isomorphism `f* M ≅ M^q` induces the corresponding tensor-power
isomorphisms, finite-cohomology equivalence, and Euler dilation. -/
def PolarizedTensorPowerEulerDilationStatement : Prop :=
  (∀ (X : Scheme.{u}) (f : X ⟶ X) (M : X.Modules) (q : ℕ)
    (_e : (Scheme.Modules.pullback f).obj M ≅ tensorPow M q) (n : ℕ),
      Nonempty (tensorPow ((Scheme.Modules.pullback f).obj M) n ≅
        tensorPow M (q * n)) ∧
      Nonempty ((Scheme.Modules.pullback f).obj (tensorPow M n) ≅
        tensorPow M (q * n))) ∧
  (∀ (K : Type u) [Field K] (X : Scheme.{u})
    (s : X ⟶ Spec (CommRingCat.of K)) (f : X ⟶ X)
    (M : X.Modules) (q : ℕ)
    (_e : (Scheme.Modules.pullback f).obj M ≅ tensorPow M q) (n : ℕ),
      (HasFiniteCohomology s (tensorPow ((Scheme.Modules.pullback f).obj M) n) ↔
        HasFiniteCohomology s (tensorPow M (q * n))) ∧
      (∀ (hF : HasFiniteCohomology s
          (tensorPow ((Scheme.Modules.pullback f).obj M) n))
        (hM : HasFiniteCohomology s (tensorPow M (q * n))),
        eulerCharacteristic s (tensorPow ((Scheme.Modules.pullback f).obj M) n) hF =
          eulerCharacteristic s (tensorPow M (q * n)) hM))

end Langlands.AlgebraicGeometry.Picard
