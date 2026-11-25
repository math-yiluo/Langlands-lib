# Algebraization from compatible diagonal coefficient systems

This module constructs a unique linear map to a direct sum from a compatible
family of linear maps to direct sums over the adic quotients. It uses the
finite-support argument of SGA 3, Exposé IX, Theorem 7.1 and Lemma 7.2,
recomposed pp.56–58 (original margins pp.68–72), registered source
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The linear interface and its packaging as `System` are internal adaptations
of the source's argument for a map between Hopf algebras.

Let `A` be a commutative ring, `I` an ideal, `C` an arbitrary `A`-module,
and `M` an arbitrary index type. These types have independent universes.
`System I` consists of linear maps

```text
fₙ : C →ₗ[A] (M →₀ A/Iⁿ)
```

whose coefficients agree under each quotient map `A/Iᵏ → A/Iⁿ` for
`n ≤ k`. The indexing includes `n = 0`, where the quotient is zero.
No group structure on `M` is required.

When `A` is `I`-adically complete and separated, `completedCoefficient`
constructs each coefficient as an element of `AdicCompletion I A`, and
`coefficients` uses the inverse of the canonical linear equivalence
`A ≃ₗ[A] AdicCompletion I A` to produce a map `C →ₗ[A] (M → A)`.
`mk_coefficients` proves its reduction equals the given coefficient at
every quotient power.

For a coefficient map `g : C →ₗ[A] (M → Q)` to an `A`-algebra `Q`,
`tensorCoefficient g m k` is the linear map from `C ⊗[A] C` to `Q` sending
`x ⊗ y` to `g(x)(m)g(y)(k)`. Reduction commutes with this map by tensor
induction. The construction assumes a linear map `d : C →ₗ[A] C ⊗[A] C`
and the following coefficient identities for every `n`, `x`, `m`, `k`:

```text
tensorCoefficient fₙ m k (d x) = if m = k then fₙ(x)(m) else 0.
```

Here the finitely supported coefficient families are included in all
coefficient families before applying `tensorCoefficient`. These equations
are the coefficient form of preservation of the diagonal group-algebra
comultiplication. The module does not assume or prove coassociativity,
counit identities, algebra structure on `C`, or a group law on `M`.

`tensorCoefficient_diagonal` passes these equations to the pointwise
limit using adic separatedness. For each `x`, the tensor
`(coefficients ⊗ coefficients)(d x)` therefore has zero off-diagonal
entries and has `coefficients(x)` on its diagonal. If `A` is noetherian,
`FiniteRankDiagonal.finite_support_diagonal` proves that this diagonal
has finite support. `System.lift` constructs the resulting linear map
`C →ₗ[A] (M →₀ A)`. Its coefficients are the limits just constructed;
`mk_lift` states their reductions, and `lift_unique` proves uniqueness
among linear maps with the specified reductions, again by separatedness.

This is a coefficient-level effectivity construction toward
`Langlands.GroupScheme.MultiplicativeTypeAdicLiftStatement`, the lifting of
homomorphisms from isotrivial groups of multiplicative type over adically
complete noetherian rings, which `multiplicativeTypeAdicLift` in
`Langlands.GroupScheme.Torus.MultiplicativeTypeAdicLiftProof` proves.
It does not itself construct algebra or Hopf homomorphisms, translate
compatible scheme morphisms into the input system, perform finite étale
descent, or prove the adic group-scheme lifting statement.
