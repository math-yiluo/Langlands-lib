# Pole regions of Weil–Deligne L-polynomials: the full statement

This module proves the published `Langlands.Global.WeilPairPoleRegionStatement`,
the formalized p-adic Weil-side cases of Henniart (1986), *On the local Langlands
conjecture for GL(n): the cyclic case*, Ann. of Math. 123, Proposition 4.5(i), p. 160
(registered source `henniart-1986-cyclic`). The two case proofs formalize the
argument in §4.7, pp. 161–162, with zero monodromy in the essentially unitary case.

```lean
theorem Langlands.Global.weilPairPoleRegionStatement :
    Langlands.Global.WeilPairPoleRegionStatement.{u, v, w}
```

The statement, in `Langlands/Global/Factors/WeilPoleRegionStatement`, is by definition
the conjunction `EssentiallyUnitaryPoleRegionStatement.{u, v, w} ∧
NonJuxtaposedPoleRegionStatement.{u, v, w}`. It is unchanged here, with its three
independent universes.

## Proof

The proof is the anonymous constructor applied to the two conjuncts, which are proved
as separately named theorems in their own modules:

- `Langlands.Global.essentiallyUnitaryPoleRegionStatement` ([proof notes](WeilPoleRegionUnitaryProof.md)).
  A common zero gives Frobenius eigenvectors on `A ⊗ B` and `A^∨ ⊗ B^∨` whose
  eigenvalues multiply to `q`. Each eigenvalue factors into eigenvalues of `Φ` or `Φ⁻¹`
  on `A` and `B`. The unitary twists make the product have modulus one: the
  character values at `Φ` and `Φ⁻¹` cancel. This contradicts `q > 1`.
- `Langlands.Global.nonJuxtaposedPoleRegionStatement` ([proof notes](WeilPoleRegionNonJuxtaposedProof.md)).
  The two zeros select a block `i` and a dual block `j`. Their eigenvectors yield
  a nonzero intertwiner, and irreducibility gives `ρ_j ≅ ν^(n_i) ρ_i`. If `i ≠ j`,
  the blocks would be juxtaposed. If `i = j`, determinants at Frobenius contradict
  the positive block length and `q > 1`.
