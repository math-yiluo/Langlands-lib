# Windows around the Levi representatives

Module `Langlands.BaseChange.TwistedLocalDescent.Windows`.

## Norm characteristic polynomials

`normCharpoly σ l B x i` is the characteristic polynomial of the norm
`x_i σ(x_i) ⋯ σ^{l-1}(x_i)` of the block `x_i`; `normCoeffs` collects its coefficients below the
leading one (`charpoly_coeff_dim`, `charpoly_coeff_eq_zero_of_lt`,
`normCharpoly_eq_of_normCoeffs_eq`). Under the hypothesis `σ^l = 1`, both are invariant under
`M(E)`-twisted conjugation `x ↦ y x σ(y)⁻¹` (`normCharpoly_twistedConj`, `normCoeffs_twistedConj`,
each with the hypothesis `σ ^ l = 1`): the norm of `y x σ(y)⁻¹` is `y N(x) σ^l(y)⁻¹`
(`cyclicNorm_twistedConj`), which is conjugate to `N(x)` when `σ^l = 1`. The hypothesis is
needed: for `E = ℂ`, `F = ℝ`, `σ` complex conjugation, `l = 1` and rank one, the norm of an
element is the element itself, and twisted conjugation of `1` by `i` gives `-1`. Over the
coefficient field `E`, coprimality of the norm characteristic polynomials of two blocks (monic
polynomials) is the nonvanishing of their resultant (`isCoprime_normCharpoly_iff`).

## Continuity

For fields `F` and `E` carrying topological-ring structures, with `E` an `F`-algebra with the
`F`-module topology, and `σ` an arbitrary `F`-algebra automorphism of `E`:
`SigmaLiftCharacterIdentity.continuous_cyclicNorm` (the norm map `g ↦ g σ(g) ⋯ σ^{l-1}(g)` on `GL_r(E)`),
`continuous_charpoly_coeff` and `continuous_resultant` (coefficients and resultants are
polynomial in the entries), `continuous_normCoeffs` and `continuous_normCharpoly_coeff`. If
moreover `E` is Hausdorff, coprimality of the norm characteristic polynomials of two blocks is an
open condition on pairs of Levi elements (`isOpen_coprime`).

## Windows

`isCoprime_charpoly_of_regular`: the blocks of a regular semisimple block diagonal element have
pairwise coprime characteristic polynomials.

`exists_windows`: under the hypotheses of the continuity results, with `E` Hausdorff and `σ` an
arbitrary `F`-algebra automorphism: for `γ` regular semisimple, a Levi class system `m` of `γ`,
`d j ∈ M(E)` with blockwise norms `m j`, and open sets `Ω j ∋ d j`, there are open `Ω' j` with
`d j ∈ Ω' j ⊆ Ω j` such that

- for `x, x' ∈ Ω' j` and distinct blocks `i ≠ i'`, `normCharpoly x' i'` and `normCharpoly x i`
  are coprime;
- for `j ≠ j'`, `x ∈ Ω' j` and `x' ∈ Ω' j'`, `normCoeffs x ≠ normCoeffs x'`.

At `x = x' = d j` the norm polynomials are those of the blocks of `m j` (base changed), pairwise
coprime by regularity; for `j ≠ j'` the tuples of characteristic polynomials of the blocks of
`m j` and `m j'` differ, since equal tuples would make `m j` and `m j'` conjugate in `M(F)`
(blockwise conjugacy of regular semisimple elements with equal characteristic polynomials), which
the Levi class system excludes. Continuity and the Hausdorff property of `E` give the windows.
