# Positivity of relative multipliers

`relativeMultiplier_pos` gives the sign that an intertwiner `S` into the Hermitian-dual
principal series must have on the compact group. The hypotheses are:

- `ds` is a list of `n` complex characters;
- its compact-finite principal series is irreducible and infinitesimally unitarizable;
- `S` intertwines this series with the series of the Hermitian-dual characters
  `ds.map hermitianData`.

Suppose that on `U(n)` the function `S v₀` is `c` times `v₀` and the function `S v₁` is
`c * r` times `v₁`, where `v₀` and `v₁` are nonzero, `c` is a nonzero complex number and
`r` is real. Then `r > 0`.

## Proof as implemented

1. `densityHyp_standard` checks the hypotheses of the Library's Schur lemma
   `GKModuleDensity.exists_eq_scalar` for an irreducible principal series. Admissibility
   comes from `isAdmissibleGKModule_principalSeriesRep`. The finite-dimensional invariant
   subspace containing a vector is its orbit span under `U(n)`. Continuity comes from the
   `(𝔤, K)`-module structure.
2. `exists_hermitianPairing_diag` compares `S` with the injective intertwiner `T` given by
   `exists_hermitianIntertwiner` for an invariant positive form `b`. For every `w` and `v`,
   `T` satisfies `hermitianPairing (T v) (conjugateStandard w) = b.inner w v`.
   `perm_hermitianData_of_irreducible_unitarizable` shows that the Hermitian-dual list is a
   permutation of `ds`. `complexStandardPermutation` then gives a bijective intertwiner `P`
   from the Hermitian-dual series back to the original series. Schur's lemma makes `P ∘ S`
   equal to `α` times the identity and `P ∘ T` equal to `β` times the identity. `β` is
   nonzero because `T` and `P` are injective and the series is nontrivial. Injectivity of
   `P` gives `S = (α / β) • T`. Hence `hermitianPairing (S v) (conjugateStandard v)` is
   `μ * b.inner v v` for every `v`, with the fixed scalar `μ = α / β`.
3. `hermitianPairing_eq_mul_integral_normSq` evaluates the same diagonal pairing in a
   second way. Let `w` agree with `a` times `v` on `U(n)`. Then the integral pairing of `w`
   with the conjugate of `v` is `a` times the integral of `|v|²` over `U(n)` with respect to
   the Haar measure.
4. `integral_normSq_pos` shows that this integral is positive for a nonzero `v`. A vector of
   the principal series vanishing on `U(n)` is zero, so `v` is nonzero at some point of
   `U(n)`. The integrand is continuous and nonnegative, and the Library lemma
   `integral_unitaryHaar_pos` applies.
5. `exists_inner_self_eq_pos` shows that `b.inner v v` is a positive real number for
   nonzero `v`, by Hermitian symmetry, positivity and definiteness of `b`.
6. Write `N₀, N₁ > 0` for the two squared `L²` norms and `B₀, B₁ > 0` for the two form values.
   Steps 2 and 3 give `c * N₀ = μ * B₀` and `c * r * N₁ = μ * B₁`. Eliminating `μ` and
   cancelling `c` gives `r * N₁ * B₀ = N₀ * B₁` in `ℝ`. The right side is positive, so
   `r > 0`.

## Provenance

This internal lemma combines two standard facts about invariant Hermitian forms on
principal series.

- On an irreducible module, an invariant form is unique up to a scalar. In the Lean proof
  this comes from Schur's lemma for admissible irreducible `(𝔤, K)`-modules, applied to two
  intertwiners.
- A form on an induced representation can be computed by integrating over the compact
  group. Vogan, *The Unitary Dual of GL(n) over an Archimedean Field*, Invent. Math. 83
  (1986), Proposition 10.5(b), p. 476, gives the induced form as `∫_K ⟨v(k), w(k)⟩ dk`. Its
  signature on `K`-types, in the sense of Definition 10.1 on p. 475, is then read off by
  restricting functions to `K`.

Here the form is given through `S` and the integral pairing. On the two vectors where `S`
is scalar on `U(n)`, its values are those scalars times positive squared `L²` norms. A
positive form therefore forces the ratio of the two scalars to be a positive real number.
