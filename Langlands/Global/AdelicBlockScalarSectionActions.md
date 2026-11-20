# Finite adelic and infinite compact actions on scalar block sections

The scalar carrier is `RealizedSections F B S` from `AdelicBlockScalarSections`. Its normalized Levi slices take values in the span of products of the supplied operator realization vectors. For a compact element \(k\), suppose \(kg=p\ell\) with \(p\) in the block parabolic and \(\ell\) in the standard compact subgroup. The normalized slice of the right translate by \(g\) at \(k\) is

\[
m\longmapsto \delta(p)^{1/2}\,\Phi_f(\ell)(m\mu(p)).
\]

`normalizedSlice_rightTranslate` proves this by evaluating the section at \((mp)\ell\), using multiplicativity of the half character, and cancelling the normalizing factor attached to \(m\).

For \(g\) in the finite adelic factor, the factorization of \(kg\) can be chosen with a finite parabolic factor. Apply finite Iwasawa decomposition to the finite component of \(kg\) and retain the infinite compact component of \(k\). Diagonal-block projection sends the resulting parabolic factor to a finite Levi element. Right translation by this Levi element preserves each product of actual block evaluations because it acts on every factor by its published finite right representation. The span is stable by linearity, proving stability of the scalar section carrier under all finite right translations.

The infinite standard compact subgroup acts on the same carrier and commutes with the finite action because the two adelic matrix factors commute. `FiniteSmoothRealizedSections` selects sections with one common open subgroup of the finite adelic factor fixing the section. The smooth part construction gives its finite representation. The infinite compact action preserves the same stabilizer. `CompactFiniteRealizedSections` further requires a finite-dimensional span of the infinite compact orbit. A finite translation intertwines the infinite compact action, so it preserves that subspace.

The actions and finiteness conditions are internal constructions on the actual scalar carrier. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the compact realization and the positive right action with the parabolic twist. Langlands (1979), proof of Proposition 2, pp. 204–206 (PDF 199–201), uses compact-finite scalar forms in the induced representation argument. The present `CompactFiniteRealizedSections` records finite smoothness and compact finiteness. Archimedean smoothness, the differential action and tensor factorization remain separate steps.
