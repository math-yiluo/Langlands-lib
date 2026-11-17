# Adic effectivity from scalar-extended bialgebra maps

Worker 891.

This module adapts genuine bialgebra maps over the adic quotients to the
coefficient-level construction of `AdicGroupAlgebra`. It implements the
scalar-extension algebra of SGA 3, Exposé IX, Theorem 7.1, recomposed
pp.56–58 (original margins pp.68–72), registered source
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The interface is internal: the source describes the same coproduct argument
with quotient Hopf algebras, whereas Lean uses tensor scalar extensions and
explicit coefficient equations.

Let `A` be a commutative ring, `C` a commutative `A`-bialgebra, `M` a
commutative additive group, and `Q` a commutative `A`-algebra. The
construction `restrict` sends a `Q`-bialgebra map

```text
F : (Q ⊗[A] C) →ₐc[Q] Q[M]
```

to the `A`-algebra map `x ↦ F(1 ⊗ x)`. The lemma
`tensorCoefficient_restrict` compares the coefficient pairing on a source
tensor with the coefficients after the tensor scalar-extension permutation.
Its proof is tensor induction. Applying this identity to the source
comultiplication, the genuine bialgebra-map coproduct equation implies
`restrict_diagonal`. The counit equation similarly gives `restrict_counit`;
there are no additional supplied coproduct or counit premises.

For an ideal `I`, `System I` consists of bialgebra maps

```text
Fₙ : ((A/Iⁿ) ⊗[A] C) →ₐc[A/Iⁿ] (A/Iⁿ)[M]
```

with agreement of the coefficients of `Fₙ(1 ⊗ x)` under each quotient map
for `n ≤ k`. `System.toAlgebraSystem` restricts these maps and supplies the
coefficient equations proved above. If `A` is noetherian and `I`-adically
complete and separated, `System.lift` constructs the actual bialgebra map
`C →ₐc[A] A[M]`. The theorem `reduce_lift` identifies its reduction on every
`x` with `Fₙ(1 ⊗ x)`, and `lift_unique` proves uniqueness among bialgebra maps
with those reductions.

The input indexing includes `n = 0`. `System.ofSucc` also accepts a family
indexed by `A/I^(n+1)` whose coefficients are compatible only for successive
powers. It inserts the canonical trivial bialgebra map at the zero quotient,
where all maps have the same values, and obtains compatibility for all
pairs of indices by the transitivity theorem for quotient factor maps.
`ofSucc_map` states that the positive-power maps are exactly the original
family.

The definition `extend` is the ordinary scalar extension of an algebra map,
followed by the standard group-algebra equivalence
`Q ⊗[A] A[M] ≃ₐ[Q] Q[M]`. `System.extend_lift` states that this full
scalar extension of the lifted map equals `Fₙ.toAlgHom`. The proof checks
pure tensors: `Q`-linearity reduces the equality on `a ⊗ x` to
`reduce_lift` on `1 ⊗ x`, and tensor induction handles all elements.
The global map is a bialgebra map; the full scalar-extension comparison is
stated as an equality of underlying algebra maps.

All four types have independent universes. No smoothness, finite-type,
flatness, or finite generation condition is imposed on `C` or `M`.
This module does not identify scheme base changes with these algebraic
systems, or perform finite étale descent; these remain separate obligations
toward the full adic group-scheme lifting theorem.
