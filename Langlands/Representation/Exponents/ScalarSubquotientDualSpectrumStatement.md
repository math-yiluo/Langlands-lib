# Scalar subquotients detected by generalized full-dual spanning

This module states
`Langlands.ScalarSubquotientDualSpectrumStatement.{uK,uA,uV,uW}`.
It contains no proof. Its coefficient field, acting group, ambient carrier and
quotient carrier have four independent universes.

Let `K` be any field, `A` any commutative group, `V` any `K` vector space,
`ρ : Representation K A V` an actual action, and `P` any predicate on
characters `A →* Kˣ`. The sole spectral hypothesis says that the supremum of
the actual generalized character subspaces of the full transpose dual action,
indexed by `χ` and proofs of `P χ`, is the entire algebraic dual
`Module.Dual K V`. The imported generalized space uses a single finite
power for each vector, valid for every element of `A`; the bound may vary with
the vector. This is the existing `generalizedCommutativeCharacterSpace`
construction, not a supplied decomposition or a finite-dimensional dual.

For every character `χ`, the proposition then considers an actual invariant
subspace `U : Subrepresentation ρ`, a nontrivial vector space `W`, and an
actual surjective linear map `q : U.toSubmodule →ₗ[K] W`. Here
`U.toSubmodule` supplies the additive and scalar structures of the invariant
subspace. Its additional hypothesis is
the scalar intertwining equation

```text
q (U.toRepresentation a u) = (χ a : K) • q u
```

for every `a : A` and `u : U.toSubmodule`. The conclusion is exactly `P χ`. Thus `q`
realizes a nonzero scalar quotient of an actual invariant subspace. Neither
the subspace nor the quotient is only a character label or an asserted
composition-factor occurrence.

There is no finite-dimensionality, finite-generation, irreducibility,
admissibility, continuity, smoothness, or finiteness-of-`P` assumption. No
topology is present. The transpose is the imported full algebraic dual action
and keeps the same character, without inversion or conjugation.

The statement is derived internal linear algebra. Its proposition body is the
interface prescribed in task `e463bc22-2bf2-4a2c-8b20-f52510b5b672`, published
as a separate prerequisite of the dual-Jacquet class-exponent comparison.
It is not a verbatim assertion from Silberger or another representation-theory
source. A proof can restrict generalized dual vectors to `U`; restriction is
surjective and preserves their characters. Pulling a nonzero functional on `W`
back through `q` produces a nonzero ordinary `χ` eigenfunctional on `U`.
Independence of simultaneous generalized weight spaces then forces `P χ`.
This paragraph describes an intended algebraic route, not a proof supplied by
this module.

The proposition does not establish its spectral spanning hypothesis, extract
an irreducible quotient, or prove the GL class-exponent equivalence. In that
application, `P` is the predicate of actual smooth ordinary dual Jacquet
exponents; the conclusion would then include both its open-kernel and ordinary
eigenoccurrence conditions. Those applications and the proof of this generic
statement are separate obligations.
