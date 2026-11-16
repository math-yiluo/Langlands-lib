# Unitary generic exhaustion

Author: Worker 4941. This file proves Task 4941
(`31c91f66-6a4d-4571-9898-e0a37589a58b`). Module
`Langlands.Representation.Classification.UnitaryGenericExhaustionProof`,
namespace `Langlands.Classification`. The proof has no `sorry` and uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

```lean
theorem Langlands.Classification.unitaryGenericExhaustion :
    UnitaryGenericExhaustion.{uF, uV} F T
```

The theorem holds for any prime `p` with `[Fact p.Prime]`, any
`F : PadicField.{uF} p` and any `T : F.TopologicalData`. The field universe `uF`
and the representation universe `uV` are independent. The theorem takes no
hypotheses. Its type is exactly the published proposition
`Langlands.Classification.UnitaryGenericExhaustion.{uF, uV} F T` from
`Langlands/Representation/Classification/UnitaryGenericStatement.lean`. That
statement and everything it imports are unchanged.

The statement says the following. Take any `n : ℕ` and any continuous nontrivial
unitary additive character `ψ`. Let `π` be an actual smooth complex representation
of `GL_(n+1)(F)` with carrier in `Type (max uF uV)`. Suppose `π` is generic for `ψ`
(irreducible, admissible, with a nonzero Whittaker functional) and unitarizable (it
has an actual positive definite invariant Hermitian form). Then there are:

- a block shape `B` of `n + 1` with positive ranks;
- actual blocks `δ i` that are irreducible, unitarizable and analytically
  square-integrable;
- real exponents `s i` with `-1/2 < s i < 1/2`.

The family `(B, δ, s)` has multiplicity-preserving Hermitian symmetry, with actual
rank-transported block isomorphisms. Finally `π` is isomorphic to the whole
normalized twisted product `T.twistedProductInduced B δ s`.

## Proof

The proof is one term with two published ingredients:

1. `tadicUnitaryDualExhaustion F T` (module
   `Classification.TadicUnitaryDualExhaustionProof`) proves
   `TadicUnitaryDualExhaustion.{uF, uV} F T` with no hypotheses. This is the
   generic-free exhaustion of Tadić 1986, Theorem D(ii). Every irreducible
   unitarizable representation of `GL_(n+1)` is isomorphic to the normalized
   product of finitely many Tadić building blocks. A building block is either a
   Speh representation or a complementary-series product `ν^α S × ν^(-α) S` with
   `0 < α < 1/2`.
2. `unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion F T` (module
   `Classification.UnitaryGenericExhaustionReduction`) proves the implication
   `TadicUnitaryDualExhaustion F T → UnitaryGenericExhaustion F T`.

Applying the second to the first gives the theorem. Both are taken at the same
`p`, `F`, `T`, `uF` and `uV`.

The reduction works as follows; its Markdown file has the details. Let `π` be
generic and unitarizable. Tadić exhaustion writes `π ≅ ∏ σ i` with building blocks
`σ i`. The Whittaker functional of `π` passes to the product and then to every
factor, by the finite-product Whittaker criterion. A generic Speh factor has Speh
length one, by `SpehDatum.length_eq_one_of_hasFunctional`. This step needs the
ordered-head classification. That classification comes from the proved
`squareIntegrableLanglandsClassification` and `segmentSpecialParameterUniqueness`.
A building block of Speh length one has a one-block or a two-block valid parameter
family: `δ` with exponent `0`, or `δ, δ` with exponents `α, -α`. These families
are assembled over the factorization and pulled back to `π` along the isomorphism.
The result is the existential statement.

## Correspondence with the sources

This follows the derivation in Henniart 2000, Appendix A.2 (printed p.453), of the
unitary generic classification from Tadić 1986, Theorem D (printed pp.338–339).
Tadić's Theorem D(ii) writes every irreducible unitary representation as a product
of `u(δ, k)` and `π(u(δ, k), α)` with `0 < α < 1/2`. Genericity of the product
forces genericity of each factor (Bernstein–Zelevinsky 1977, §§4.5–4.7). A generic
`u(δ, k)` has `k = 1` (Zelevinsky 1980, Theorem 9.7 and §9.10). With `k = 1` the
factors are `δ` and `ν^α δ × ν^(-α) δ`. Collecting them gives exponents in the
open interval `(-1/2, 1/2)` with Hermitian symmetry. In the Lean proof, Tadić's
theorem is the published theorem `tadicUnitaryDualExhaustion`. Its Markdown file
describes how its own proof is assembled.
