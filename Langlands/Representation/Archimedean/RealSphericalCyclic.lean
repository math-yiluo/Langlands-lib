import Langlands.Representation.Archimedean.RealTemperedCommutantReduction
import Langlands.Representation.Archimedean.RealGenericParameterReduction

/-!
# Cyclicity of the spherical vector of a real unramified principal series

Statement only. For real characters of parity `0` (so of the form `x ↦ |x|^e`) whose exponents
have weakly decreasing real parts, every nonzero `O(n)`-fixed vector of the `O(n)`-finite
functions of the real standard module generates the whole space under the complexified Lie
algebra action. This is the `GL_n(ℝ)` case of Kostant's cyclicity theorem for the spherical
vector in the closed positive chamber.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open scoped TensorProduct

/-- Spherical cyclicity in the closed Langlands chamber. Let `ds` be a list of `n` real
characters, all of parity `0`, whose exponents have weakly decreasing real parts
(`IsRealLanglandsOrdered`). Let `T` be a nonzero `O(n)`-fixed vector of the `O(n)`-finite
functions of the real standard module of `ds`. Then every complex subspace `W` of these
functions that contains `T` and is stable under the action `realStandardLie` of
`ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` is the whole space. Stability of `W` under `O(n)` is not assumed. -/
def RealSphericalCyclicStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealCharacterData), ds.length = n →
    (∀ d ∈ ds, d.parity = 0) →
    IsRealLanglandsOrdered (ds.map RealBlock.character) →
    ∀ T : RealTemperedCommutantReduction.KF n (ds.map RealBlock.character),
      (∀ k, realStandardRep n (ds.map RealBlock.character) k T = T) → T ≠ 0 →
      ∀ W : Submodule ℂ (RealTemperedCommutantReduction.KF n (ds.map RealBlock.character)),
        T ∈ W → (∀ Z, ∀ w ∈ W, realStandardLie n (ds.map RealBlock.character) Z w ∈ W) →
        W = ⊤

end Langlands.Archimedean
