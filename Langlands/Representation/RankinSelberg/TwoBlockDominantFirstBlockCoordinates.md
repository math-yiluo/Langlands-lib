# First-block rectangle coordinates for the dominant calculation

Worker 113. This internal helper supplies the elementary row substitution in
the first-block calculation of JPSS (1983), Section 4.9, printed pages 416–418,
as used in Section 4.10(2), printed page 419. The original is registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The particular coordinate interfaces and their general dimensions are derived
infrastructure, rather than separately stated assertions in the paper.

With the ordered blocks `(a,b,j)`, the proved three-block multiplication is

```text
[1,0,0;0,1,0;U,Y,1] diag(v,1,1) [1,0,0;Z,1,0;0,0,1]
  = [v,0,0;Z,1,0;Uv+YZ,0,1] [1,0,0;0,1,0;0,Y,1].
```

Here `Z` is `b×a`, `U` is `j×a`, and `Y` is `j×b`. The matrix identity is
proved over any commutative ring by the existing complete three-block
multiplication lemma. It identifies the small rectangle as the rows `Z`
followed by `T=Uv+YZ`.

`firstBlockRowChange v Z Y` is the actual homeomorphism from `U` to `T`,
with inverse `(T-YZ)v⁻¹`. For every p-adic field with its canonical
topological data and every supplied scalar additive Haar measure `ν`,
`rectangularMeasure_map_firstBlockRowChange` proves the pushforward formula
with factor `|det v|⁻ʲ`. The proof first applies the published rectangular
Haar scaling theorem to right multiplication by `v` and then uses translation
invariance. No replacement Haar measure is chosen.

`integral_firstBlockRowChange` and `integrable_firstBlockRowChange_iff`
separately give the total Bochner substitution and the equivalence of actual
integrability. `firstBlockRectangleChange` keeps `Y` and applies the change
to `U`; its joint measure-preserving statement has the scaled measure in
the second target coordinate and follows by the measurable skew-product
theorem. Zero row and column dimensions are retained.

This helper does not assert quotient disintegration, convergence of the
dominant lower kernel, a functional equation, or a Laurent identity.
