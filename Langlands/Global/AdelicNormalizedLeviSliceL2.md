# Square integrability of the individual normalized Levi slices

Let \(P=MU\) in \(G\), let \(K\subset G(\mathbb A)\) be maximal compact, and
write \([M]=A_M M(F)\backslash M(\mathbb A)\). For a square-integrable
inducing form \(\phi\), the normalized value `normalizedLeviValue p l φ m k`
represents the slice
\[
m\longmapsto m^{-\rho_P}\phi(mk).
\]
`memLp_normalizedLeviValue_slice` proves that for every \(k\in K\) this slice
is in \(L^2([M])\) for `canonicalMeasure F M`.
`normalizedLeviSliceL2` proves the proposition `NormalizedLeviSliceL2Statement`
by applying this lemma. Both use the given compact, the square-integrability
predicate of `AdelicSquareIntegrableInducedForms` and connected reductivity of
the Levi.

## Proof

A maximal compact of the adelic group factors as \(K_\infty\times K_f\).
The inducing function is fixed on the right by an open subgroup \(L\) of the
finite adelic group. Hence the translates by \(K_f\) are indexed by the finite
set \(K_f/(K_f\cap L)\). The infinite and finite factors commute. The right
translates by \(K\) thus lie in the sum of the finitely many translates by
coset representatives of the finite-dimensional \(K_\infty\)-orbit span.
This proves `finiteDimensional_compactRightTranslateSpan_of_adelicSmooth`.

Left invariance under \(A_M\) and \(M(F)\) descends the continuous normalized
value to a jointly continuous function on \(K\times[M]\). Connected reductivity
gives finite volume for the canonical measure on \([M]\). The squared absolute
value is Lapid's weighted square, so the joint integrability in the definition
of \(\mathcal A^2_P\) gives \(L^2\) on \([M]\) for almost every \(k\) by Fubini.
The linear map which restricts a function to the Levi and multiplies by
\(m^{-\rho_P}\) sends the full compact orbit span into a finite-dimensional
space of functions on \([M]\). Within this space the \(L^2\) functions form a
linear subspace. It is finite dimensional and therefore closed in the
pointwise topology. The map sending \(k\) to the normalized slice is
continuous in that topology, so the set of \(k\) with \(L^2\) slices is
closed. It is also conull and the Haar probability gives positive mass to
each nonempty open set. Thus it contains every \(k\in K\).

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
  Series* (1995), I.2.17, printed p. 37
  (`moeglin-waldspurger-1995-growth-and-constant-terms`), gives the
  half-modulus-normalized slice at compact arguments.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series* (2011), §2, printed p. 311
  (`lapid-2011-asymptotic-inner-product-truncated-eisenstein`), gives the
  square-integrability condition and relates the inducing space to
  \(L^2\) on the Levi quotient. The individual-slice assertion follows
  from that condition by the finite-dimensional argument above.
