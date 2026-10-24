# Uniform root expansions for coefficient models

`Langlands.RankinSelberg.EqualRankRootExpansionStatement F T n` is a
conditional internal interface for the actual equal-rank coefficient models.
It preserves the supplied topology `T`, the normalized absolute value, the
independent universes of the field and two representation spaces, and every
rank `n + 1`, including rank one.

Fix two representations `π` and `σ` and a nontrivial unitary additive
character `ψ`. The hypotheses are the published
`CoefficientTorusExpansion` propositions for `π` with the standard character
and `σ` with the inverse character. These hypotheses include uniform finite
sets of continuous translation-finite functions on the full diagonal torus.
They are explicit prerequisites: this statement does not assert that the
expansions have been proved for Whittaker-type representations.

For a unit vector `a`, write

\[
d(a)_i=\prod_{j\geq i}a_j,\qquad
w(a)=\left(\prod_{i=0}^{n}|a_i|_F^{(i+1)(n-i)}\right)^{-1}.
\]

The conclusion first chooses a natural number `m` and a family of functions
`η_j` on the full unit torus, indexed by `Fin m`. Each `η_j` is continuous,
and the complex span of its left translates `a ↦ η_j(b*a)` is
finite-dimensional. This family is fixed before either equivariant
functional, either model coefficient, the row test or the matrix `k`.
Different indices may give the same function; the finite image of the family
therefore supplies a finite set of functions independent of all these data.

For every such pair of functionals `ℓ, ℓ'`, actual model coefficients
`f, f'`, Schwartz–Bruhat row test `Φ`, and invertible matrix `k`, there are
Schwartz–Bruhat functions `Ψ_j` on the full field space `F^(n+1)` satisfying

\[
 f(\operatorname{diag}(d(a))k)\,
 f'(\operatorname{diag}(d(a))k)\,
 \Phi(\operatorname{lastRow}(\operatorname{diag}(d(a))k))\,w(a)
 =
 \sum_{j=0}^{m-1}\Psi_j((a_i)_i)\eta_j(a).
\]

The identity holds at every unit vector. In particular, `k` need not lie in
a compact subgroup. No nonzero-functional assumption is required; zero
coefficients, empty finite families and rank one remain in scope.

The provenance is an internal combination of the coefficient-model action
and `RootTorusProductStatement`. The right action on the actual coefficient
image sends `f` to the function `g ↦ f(g*k)`. Apply the two assumed torus
expansions to these translated model elements. Their finite-function sets
are unchanged by this choice of elements. The uniform product reduction
then combines the two root tests and the row test with the inverse modulus.
An enumeration of its finite product index set gives `Fin m`. This explains
both the formula and the order of its quantifiers.

This is a pointwise reduction. It contains no spectral parameter or
integration assertion. The quotient Iwasawa formula, Mellin convergence and
uniform rational denominator, and normalized-generator existence are
separate obligations. No independent theorem from the literature is
attributed to this elementary adapter. The Lean file defines its proposition
target.
