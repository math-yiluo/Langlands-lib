# Actual matrix bridges for the dominant first-block calculation

Worker 113. Derived coordinate infrastructure for the first-block route of
JPSS (1983), Sections 4.9 and 4.10(2), printed pages 416–419, registered as
`jpss-1983-rankin-selberg` with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These finite matrix identities are internal deductions from the published
JPSS block definitions and are not claimed to be separately stated source
results.

Write `a = m 0 + 1`, `b = m 1 + 1`, and `c = j + k + 1`, so that
`a + b = t + 1`. The equivalence `firstBlockCoordinates` reads the actual
ambient rank as the three ordered blocks of sizes `a`, `b`, and `c`.
`firstBlockForm` is simultaneous submatrix reindexing by this equivalence;
it is injective and preserves multiplication and the identity.

`firstBlockColumns h j U Y` joins the external columns `U` and `Y` in
rank `t+1`. The coordinate lemmas establish the forms of the actual rank
inclusion, first-block Levi embedding, lower radical, and rectangular
unipotent. In these coordinates they are respectively the section's four
entry blocks with an identity tail, `diag(v,1,1)`,
`[1,0,0; Z,1,0; 0,0,1]`, and
`[1,0,0; 0,1,0; stackRows U,stackRows Y,1]`.

`firstBlockRows j Z T` joins `Z` and `T` in that order into `b+j` rows.
`firstBlockSmallMatrix h j k v Z T` is precisely the published actual
`unequalRankMatrix (b+j) k v` evaluated on those rows, with its rank
transported by the arithmetic equality to the original ambient rank.
The theorem `firstBlockForm_smallMatrix` proves its form
`[v,0,0; Z,1,0; stackRows T,0,1]`, including the final `k+1`
identity rows.

The resulting theorem `firstBlock_matrix_factorization` proves the actual
invertible-matrix equality

```
R(U,Y) * diag(v,I_b,I_c) * diag(lowerRadical(Z),I_c)
  = firstBlockSmallMatrix(v,Z,U*v+Y*Z) * R(0,Y).
```

Here `R(U,Y)` abbreviates only the displayed published rectangular
unipotent with joined columns, and the middle factor uses the actual
`firstBlockEmbedding`. The proof applies injectivity of `firstBlockForm`,
rewrites all four actual matrix forms, and uses
`firstBlock_three_factorization` from the affine-coordinate helper.
A pointwise calculation verifies that padding the external rows commutes
with the rectangular products and their sum.

All identities hold over an arbitrary field for arbitrary natural `j,k`,
including `j=0`, and all positive section block sizes. The module changes
no measures and asserts no integrability or Laurent identity. Quotient
disintegration, section coefficients, spectral weights, and the common
first-block functional equation remain subsequent steps of the host task.
