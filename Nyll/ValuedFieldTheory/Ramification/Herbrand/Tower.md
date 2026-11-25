# The group-theoretic step of Herbrand's theorem

Module `Nyll.ValuedFieldTheory.Ramification.Herbrand.Tower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Herbrand's theorem on quotients rests on one observation about the ramification depth `i(σ) = v(σ(a) − a)`: in a nontrivial coset `σH`, a representative of maximal depth satisfies `i(στ) = min(i(σ), i(τ))` for every `τ ∈ H`. The file proves this for any depth function with the relevant non-archimedean properties, with no valuation in sight.

## Main definitions and results

- `NonarchimedeanDepth G`: a structure with `depth : G → WithTop ℕ` such that `depth σ = ⊤` exactly when `σ = 1`, `depth (στ) ≥ min(depth σ, depth τ)`, equality holds when the two depths differ, and depth is invariant under conjugation.
- `QuotientFiber H q`: the elements of `G` mapping to `q ∈ G/H`, for a normal subgroup `H`. On a nontrivial fibre the depth is finite, and `quotientFiberDepth` reads it as a natural number.
- `exists_maximal_depth_representative`: for finite `G` and `q ≠ 1`, the fibre over `q` has an element of maximal depth.
- `depth_mul_eq_min_of_maximal_representative`: if `σ` has maximal depth in its fibre, then `depth(στ) = min(depth τ, depth σ)` for all `τ ∈ H`. `exists_representative_depth_mul_eq_min` combines the two results.
- Summation tools: `rightCosetEquivQuotientFiber` (`τ ↦ στ` identifies `H` with the fibre of `σ`), `card_quotientFiber`, `sum_quotientFiber_eq_sum_subgroup`, and `sum_quotientFiber` (a sum over `G` is the sum over `G/H` of the sums over the fibres).
- `sum_depth_quotientFiber_eq_sum_min_of_maximal_representative` and `exists_representative_sum_depth_eq_sum_min`: for finite `G`, any `f` with values in an additive commutative monoid and `σ` of maximal depth in its fibre, the sum of `f(depth γ)` over the fibre equals the sum over `τ ∈ H` of `f(min(depth τ, depth σ))`. The second lemma says that every `q ≠ 1` has a representative `σ` for which this holds.

## Proofs

The key identity compares `depth τ` with `depth σ`: if they differ, the axiom on unequal depths gives the minimum; if they are equal, maximality of `σ` gives one inequality and the minimum law the other.

## Watch for

- The non-archimedean laws are fields of `NonarchimedeanDepth`, not derived from a valuation; the file builds no instance from a field extension.
- The remaining valued-field input, that the depth of the image in the quotient is the normalized sum of the depths over the fibre, is neither proved nor assumed here. The docstring says so explicitly, and Herbrand's theorem itself is not stated in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Herbrand/Tower.lean`: the Lean file is the source byte for byte (SHA-256 `81689e07ca6fecdc0a0b9dc53245748368df3b86f5437bc559ed374a54257594`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
