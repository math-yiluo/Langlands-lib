import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleSplit

/-!
# Swapping two adjacent unlinked characters of a complex standard module

`ComplexStandardUnlinkedSwapStatement` says: if two adjacent characters `d`, `e` of a list of
`n` complex characters are not linked (`IsComplexLinked`), then swapping them does not change
the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite functions of the standard module, up to a
bijective intertwining map. There is no condition on the real parts of the exponents and none on
the order of the other characters.

Source (Tadić 2009): `δ_d × δ_e` is irreducible when `δ_d`, `δ_e` are not linked (p. 11); an
irreducible `σ₁ × σ₂` is isomorphic to `σ₂ × σ₁` (p. 6, after (1-2)); induction in stages
(1-1) (p. 5–6) then gives `σ × (δ_d × δ_e) × τ ≅ σ × (δ_e × δ_d) × τ`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

-- As in `ComplexLargeStandardIrreducibleSplit`: the charts on units need reduction through the
-- normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

/-- **Swapping adjacent unlinked characters** (Tadić 2009, p. 11, p. 6 after (1-2), and
(1-1) on pp. 5–6): for lists `pre`, `post` and complex characters `d`, `e` with
`(pre ++ d :: e :: post).length = n` and `d`, `e` not linked, there is a bijective
intertwining map from the `U(n)`-finite functions of the standard module of
`pre ++ e :: d :: post` onto those of the standard module of `pre ++ d :: e :: post`. -/
def ComplexStandardUnlinkedSwapStatement : Prop :=
  ∀ (n : ℕ) (pre post : List ComplexCharacterData) (d e : ComplexCharacterData),
    (pre ++ d :: e :: post).length = n → ¬ IsComplexLinked d e →
      ∃ T : kFiniteFunctions (complexStandardModule n (pre ++ e :: d :: post))
            (unitaryCompact ℂ n) →ₗ[ℂ]
          kFiniteFunctions (complexStandardModule n (pre ++ d :: e :: post))
            (unitaryCompact ℂ n),
        Function.Bijective T ∧
          IsComplexStandardIntertwining n (complexStandardRep n (pre ++ d :: e :: post))
            (complexStandardLie n (pre ++ d :: e :: post)) (pre ++ e :: d :: post) T

end Langlands.Archimedean
