# Dual pair-block Euler formulas from the ordinary formulas

The proposition `Langlands.LocalFactor.WDEulerDualPairBlockReductionStatement`
and its proof `wdEulerDualPairBlock_of_pairBlock` give the implication

```lean
WDEulerPairBlockStatement.{uK, uG, max uK uV, max uK uW} →
  WDEulerDualPairBlockStatement.{uK, uG, uV, uW}
```

The coefficient, group and two original carrier universes are independent.
The larger carrier universes in the premise are required because the actual
algebraic dual of a carrier in `Type uV` lies in `Type (max uK uV)`.
For complex coefficients (`uK = 0`) these maxima reduce to the original
carrier universes.

This is an internal deduction from the published ordinary pair-block target,
actual block-duality equivalences and Euler invariance. The ordinary formula
remains a premise. This unit does not prove that formula or the assembly
epsilon-inheritance target, and it introduces no local-constant or analytic
existence assertion. No additional source assertion is used.

## Tensor twists and actual invariant subspaces

For a field `K`, a group `G`, two finite-dimensional representations `A`, `B`
and characters `χ`, `ψ : G →* Kˣ`, `tensor_twist_action` proves that the
action on the tensor of the twisted representations is
`(χ(g) * ψ(g))` times the action on `A ⊗ B`.
The proof applies the tensor-map scalar identities with explicit linear maps.

For a normal subgroup `I` on which both characters are trivial,
`invariantsTensorTwistEquiv` is the identity on ambient tensor vectors and
identifies the two actual fixed subspaces. Both directions are proved from
the tensor-action identity. Invariants are taken after tensoring; no
identification with a tensor of separate invariant spaces is asserted.

`invariantsTensorTwist_conj` shows that conjugation through this linear
equivalence takes the operator
`(c * (χ(g) * ψ(g))) • (A ⊗ B)^I(g)` to the operator
`c • ((χ ⊗ A) ⊗ (ψ ⊗ B))^I(g)`.
The notation `χ ⊗ A` here means the scalar character twist on the same
carrier. `eulerPolynomial_invariantsTensorTwist` then follows from the
published conjugation invariance of the Euler polynomial. These helpers
hold without a characteristic-zero assumption.

## Dual block calculation

The main proof fixes all the data quantified in the dual pair-block target,
including the characteristic-zero field, the normal subgroup `I`, the
inertia-trivial norm character `ν`, the element `Φ`, representations `A`,
`B`, and natural numbers `n`, `m`.

The published `WeilDeligneRepresentation.Blocks.blockDualEquiv` identifies
the dual of the uncentered block of length `n+1` with the block of the same
length whose Weil factor is `dual A` twisted by `ν^(1-(n+1)) = ν^(-n)`.
Tensoring the two block equivalences produces an actual Weil–Deligne pair
equivalence. Its restriction to the inertia-fixed monodromy kernels
preserves their Euler polynomials and ranks.

Apply the supplied ordinary pair-block formula to the twisted dual Weil
factors. Both twists are trivial on `I`, so the preceding invariant-space
comparison removes them from the carrier and puts their values into the
scalar operator. For each `j < min(n+1,m+1)`, the resulting exponent is

```text
(n + m - j) + (1 - (n + 1)) + (1 - (m + 1)) = -j.
```

The private scalar lemma proves this identity in the unit group, then maps
it into `K`. The bound on `j` justifies converting the natural subtraction
in the ordinary exponent to integer subtraction. Thus the Euler polynomial
is exactly the product of the target factors with integer exponents `-j`.

The rational-factor equality follows by applying the polynomial algebra map,
taking reciprocals, and distributing over the finite product. The rank
formula follows from the kernel equivalence, the rank conjunct of the
ordinary formula, and `invariantsTensorTwistEquiv.finrank_eq`. This proves
all three conjuncts of the unchanged dual pair-block proposition, including
zero-dimensional Weil factors and lengths starting at one.
