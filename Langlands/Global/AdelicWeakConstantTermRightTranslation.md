# Infinite right translation of weighted forms and weak constant terms

`AdelicWeakConstantTermRightTranslationStatement` takes a logarithmically square-integrable
automorphic form and an infinite adelic point `a`. The right translates of the form by the
archimedean pullback of `K` must span a finite-dimensional complex vector space, as in the
compact-finiteness condition of Delorme §3.1, PDF p. 9. The right translate `g ↦ φ(g a)`
satisfies the same weighted automorphy predicate for the conjugate subgroup `a K a⁻¹`. The
right translate of each supplied weak constant term of `φ` is a weak constant term of
`g ↦ φ(g a)` at the same standard parabolic. The theorem
`adelicWeakConstantTermRightTranslation` establishes both assertions.

The weight is `rationalLogHeight` for the supplied matrix representation. For a closed matrix
embedding, as in `TemperedWeakConstantTermVanishingStatement`, it realizes the quotient
logarithmic height of Delorme, *On the spectral theorem of Langlands* (2023), §2, (2.6)–(2.8),
PDF p. 8, up to equivalence of weights. The input bounds the weighted `L²` norm of the form
itself. Delorme's `[G]`-temperedness, used in the discussion before Lemma 7.10, asks also for
weighted bounds on the derivatives as in Proposition 3.5, PDF p. 12. Weak constant terms use the
decomposition (3.2), PDF p. 10, and Definition 3.7,
PDF p. 13. These locators refer to `Delorme--On the spectral theorem of Langlands--2023.pdf`,
file SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, registered under
`delorme-2023-spectral-theorem-langlands`.

Right translation on the rational quotient preserves Haar measure. The matrix height of a
product is bounded by the height of the first factor times a constant for the fixed right
factor. Taking the infimum over the rational representatives and then the logarithm bounds the
shifted quotient height by a constant times the original one. The rank-zero matrix case uses
the constant matrix height. Comparing the weight before and after the measure-preserving
translation gives the translated `L²` condition with the same logarithmic exponent. The left
split-component character is preserved, and the automorphy condition uses the archimedean
pullback of the conjugate subgroup.

Right translation commutes with the unipotent integrals and with the left split-component
action. It transports each automorphic component of a constant-term decomposition with its
exponent unchanged. The sum over unitary labels therefore gives the translated weak term.

## Weak constant terms for an adelic maximal compact

`WeakConstantTermCompactTranslationStatement` gives the corresponding result for a maximal compact. Let \(a\in G(F_\infty)\) and let \(t\in G(\mathbb A_F)\) be its infinite
inclusion, with finite components equal to one. If \(\psi\) is the weak
constant term of \(\Phi\) along a standard parabolic for a maximal compact
\(K\), then \(g\mapsto\psi(gt)\) is the weak constant term of
\(g\mapsto\Phi(gt)\) for the conjugate compact \(t K t^{-1}\).

In the generalized-exponent condition, the split component acts on the left.
The same polynomial at \(gt\) works for the translated function at \(g\),
so the exponent and its degree bound persist. The unipotent integral also
commutes with right translation since its integrand becomes
\(\Phi((ng)t)=\Phi(n(gt))\). Translate each component of the finite
constant-term decomposition. The automorphy theorem for infinite right
translation supplies the conjugated infinite compact for each component.
The filter on the exponent set is unchanged by the translation, giving the
claimed identity for the sum of the unitary components. The theorem for an
adelic maximal compact identifies the infinite projection of its conjugate
with the conjugate of its infinite projection.

The construction uses P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, (3.2), p. 10, and Definition 3.7,
p. 13. It gives a change of compact for the weak term in the argument of
Theorem 7.9, pp. 33–35. The published PDF in
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
