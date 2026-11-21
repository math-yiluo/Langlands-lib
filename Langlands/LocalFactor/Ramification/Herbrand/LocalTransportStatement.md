# Transport of the Herbrand filtration in either characteristic

Both proposition definitions are in `Langlands.Ramification.Local` and
are targets for later proofs.

## Finite transport

`FiniteHerbrandTransport` concerns a \(K\)-algebra equivalence
\(f:L_1\cong L_2\) in compatible towers \(K_0\to K\to L_i\) over a common
valued base with topology. Each \(L_i/K_0\) is finite and each realization
\(T_i\) is supplied as `LocalField.TopologicalData K₀ Lᵢ`. The statement
asserts that `f.autCongr` carries membership in the natural and integer lower
groups and the real upper groups in both directions. It also asserts equality
of the natural lower group orders and pointwise equality of \(\varphi\) and
\(\psi\). The integer clauses range over all integers and the real clauses
range over all reals, using the extensions of the source conventions already
implemented in the Library.

## Ambient transport

`AmbientUpperRamificationTransport` states the membership equivalence in
`upperGroupIn` at every real index under conjugation by a \(K\)-algebra
equivalence \(\Omega_1\cong\Omega_2\) in compatible towers
\(K_0\to K\to\Omega_i\). The common base \(K_0\) is complete and locally
compact with a nontrivial ultrametric norm. The hypothesis `hbase` identifies
norm comparison with the supplied valuative comparison, and \(K/K_0\) is
finite. In each ambient field, `upperGroupIn` is the intersection of the
restriction preimages of the canonical upper groups of its finite Galois
subfields over \(K\). For a separable closure this intersection unfolds to
`absoluteUpperRamificationGroup`.

## Provenance

The finite statement is a naturality consequence of the action on the
integer-ring quotients in Serre, *Local Fields* (1979), Chapter IV, §1,
Lemma 1(a) and Proposition 1, printed pp. 61–62, and of the definitions of
\(\varphi\), \(\psi\) and upper numbering in §3, printed pp. 73–74. The
integer-ring isomorphism carries powers of the maximal ideal to the
corresponding powers and intertwines the actions by conjugation. The matching
lower group orders determine \(\varphi\), whose inverse is \(\psi\).

The ambient statement uses the finite tests from Serre's inverse-limit
construction in Chapter IV, §3, Remark 1, printed p. 75. The Library extends
those tests to arbitrary ambient fields, and an ambient equivalence pairs the
finite Galois subfields by pullback. These transport statements use the
characteristic-free `GeneralTransport` interface and follow the conjugation
direction of the p-adic theorems in `TransportProof.lean`.

The registered source `serre-1979-local-fields` is the 1979 English edition,
SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
