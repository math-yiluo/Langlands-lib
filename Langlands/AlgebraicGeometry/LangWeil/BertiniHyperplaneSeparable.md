# The generic linear form and the field-theoretic Bertini lemma

Author: Worker 205.

This internal helper module is the first step of the proof of
`Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplaneStatement`. It works with a
field `K` over a field `k`, a family `g : Fin N → K`, the polynomial ring `K[x_0, …, x_{N-1}]`,
its fraction field `K(x)`, and the generic linear form `ξ = ∑ gᵢ xᵢ`.

## Declarations

- `algebraicIndependent_snoc`: if `v : Fin N → A` is algebraically independent over `R` and
  `a` is transcendental over the subalgebra `R[v]`, then `Fin.snoc v a` is algebraically
  independent. Proof: Mathlib's `AlgebraicIndependent.option_iff`, transported along
  `finSuccEquivLast`.
- `algebraicIndependent_option_linearForm`: if `![g j, g l]` is algebraically independent
  over `k`, then in `K[x]` the family indexed by `Option (Option (Fin N))` with entries
  `ξ = ∑ C(gᵢ) Xᵢ`, `C(g j)` and `X_0, …, X_{N-1}` is algebraically independent over `k`.
- `algebraicIndependent_snoc_linearForm`: the same family in `K(x)`, ordered as
  `(x_0, …, x_{N-1}, ξ, g j)` (`Fin.snoc` twice), as required by the Library's field Bertini
  lemma.
- `mem_adjoin_of_isSeparable`: let `k` be algebraically closed, `K` finitely generated as a
  field over `k` (`(⊤ : IntermediateField k K).FG`), `g : Fin (m + 1) → K` and `![g j, g l]`
  algebraically independent over `k`. Then every element of `K(x)` that is separable over
  `k(x, ξ)` lies in `k(x, ξ)`.

## Proof of the independence statement

The variables `X` are algebraically independent over `K`, and `g j, g l` over `k`. By Mathlib's
`AlgebraicIndependent.sumElim_comp`, the family `(X, g j, g l)` is algebraically independent
over `k` in `K[x]`. Hence `(X, g j)` is algebraically independent and `g l` is transcendental
over `S = k[X, g j]`.

Let `σ` be the `K`-algebra automorphism `X_l ↦ X_l + 1`, `Xᵢ ↦ Xᵢ` for `i ≠ l`. Its inverse is
`X_l ↦ X_l - 1`, so `σ` is injective. It maps `S` into `S`, and `σ(ξ) = ξ + g l`. Suppose `ξ`
were algebraic over `S`. Mathlib's `IsAlgebraic.ringHom_of_comp_eq` transfers this along the
injective restriction of `σ` to `S`, so `ξ + g l` is algebraic over `S`. Subtracting gives that
`g l` is algebraic over `S`, a contradiction. Thus `ξ` is transcendental over `S`, and
`AlgebraicIndependent.option_iff` adds `ξ` to the independent family `(X, g j)`.

The family is mapped into `K(x)` by the injective map `K[x] → K(x)`
(`AlgebraicIndependent.map'`) and reindexed with an explicit equivalence
`Fin (N + 1 + 1) ≃ Option (Option (Fin N))`.

## Proof of the separability statement

The Library's field Bertini lemma
`IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent` (ported from the
Anthropic FLT formalisation) has hypotheses: `K` finitely generated over `k`, `k` separably
closed in `K`, and `x`, `∑ gᵢ xᵢ`, `∑ cᵢ gᵢ` algebraically independent over `k`. Its
conclusion is that `k(x, ∑ gᵢ xᵢ)` is separably closed in `K(x)`. We apply it with
`c = Pi.single j 1`, so that `∑ cᵢ gᵢ = g j`. The previous paragraph gives the independence
hypothesis. Separable closedness of `k` in `K` holds because `k` is algebraically closed
(Library helper `P2MW.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime.P2mIrredHyp.mem_bot_of_isSeparable`).
The Library lemma is stated for an infinite `k`; an algebraically closed field is infinite.

## Provenance

Internal, derived from the Stacks Project, Section 37.32 "Bertini theorems" (Tag 0G4C):
Lemma 37.32.1 (Tag 0G4D) is the field Bertini lemma used here through its Library port.
Stacks obtains the independence of `x`, `ξ` and a linear combination `∑ cᵢ gᵢ` from
Lemma 37.32.2, a dimension count. This module replaces that lemma by the shift argument above,
which needs two algebraically independent entries of `g`. The shift `x_l ↦ x_l + 1` is the
automorphism `σ_a` used in the proof of Lemma 37.32.1, with `a = 1` and `c = Pi.single l 1`.
