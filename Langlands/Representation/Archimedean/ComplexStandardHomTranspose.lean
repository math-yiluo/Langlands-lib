import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction

/-!
# Transposition of intertwinings between complex principal series

`ComplexStandardHomTransposeStatement` says: a nonzero `(𝔤, K)`-intertwining map from the
`U(n)`-finite functions of the principal series of `d` to those of `c` gives a nonzero
intertwining map from the principal series of the pointwise inverse characters `c⁻¹` to that
of `d⁻¹` (the transpose under the contragredient dualities `X(c)^∨ ≅ X(c⁻¹)`,
`X(d)^∨ ≅ X(d⁻¹)`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

/-- Transposition of intertwinings between complex principal series. A nonzero
intertwining map from the `U(n)`-finite functions of the standard module of `d` to those of `c`
gives a nonzero intertwining map from the standard module of the pointwise inverse characters
`c⁻¹` to that of `d⁻¹` (the transpose under the contragredient dualities
`X(c)^∨ ≅ X(c⁻¹)`, `X(d)^∨ ≅ X(d⁻¹)`). -/
def ComplexStandardHomTransposeStatement : Prop :=
  ∀ (n : ℕ) (d c : Fin n → ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n (List.ofFn c)) (unitaryCompact ℂ n)),
    T ≠ 0 →
      IsComplexStandardIntertwining n (complexStandardRep n (List.ofFn c))
        (complexStandardLie n (List.ofFn c)) (List.ofFn d) T →
      ∃ T' : kFiniteFunctions
          (complexStandardModule n (List.ofFn fun j => complexCharacterDataInv (c j)))
          (unitaryCompact ℂ n) →ₗ[ℂ]
        kFiniteFunctions
          (complexStandardModule n (List.ofFn fun j => complexCharacterDataInv (d j)))
          (unitaryCompact ℂ n),
        T' ≠ 0 ∧
          IsComplexStandardIntertwining n
            (complexStandardRep n (List.ofFn fun j => complexCharacterDataInv (d j)))
            (complexStandardLie n (List.ofFn fun j => complexCharacterDataInv (d j)))
            (List.ofFn fun j => complexCharacterDataInv (c j)) T'

end Langlands.Archimedean
