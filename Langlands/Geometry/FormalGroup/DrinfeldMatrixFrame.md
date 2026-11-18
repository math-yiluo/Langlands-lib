# Chosen matrix coordinates on an actual special formal frame

This construction models a choice explicitly made by Drinfeld: matrix algebra
coordinates on the actual rational full-order endomorphisms of the fixed
special formal frame. It turns invertible matrices into actual rational
quasi-isogenies and extends these maps to the actual source atlas of a framed
representative.

The source motivation is Drinfeld, *Coverings of p-adic symmetric regions*
(1976), §2 A, printed p.109 (PDF page 3), in the paragraph fixing the special
frame `Φ` and an isomorphism from the degree-`d` matrix algebra to its rational
endomorphism algebra. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The paragraph is motivation for the chosen-coordinate input; the present
construction does not prove the source's existence or classification claim.

The hypotheses are a nonarchimedean local field `K`, a finite-dimensional
central division algebra `D`, supplied embedded and residue fields, and an
actual special formal module `Φ`. Its coordinate dimension is
`d = CentralSimple.reducedDegree K D`.
`SpecialModule.MatrixCoordinates Φ` is exactly an actual `K`-algebra
equivalence from `Matrix (Fin d) (Fin d) K` to the existing actual rational
formal centralizer `RationalHom K Φ.order Φ.order`. It contains no abstract
group action, representing object or universal object. No such equivalence is
asserted to exist for arbitrary supplied coefficient fields or division
algebras. In particular, the specialness and height hypotheses alone are not
used to infer its existence.

For chosen coordinates `c`, `unitEquiv` restricts this algebra equivalence to
the actual unit groups. `quasiIsogenyEquiv` then uses the proved equivalence
between units of the actual rational endomorphism ring and actual self
quasi-isogenies. Consequently `quasiIsogeny c g` has forward map exactly
`c(g)` and inverse map exactly `c(g⁻¹)` in the original rational formal Hom.

The identity, product and inverse equations follow from preservation of the
actual ring operations. The product convention is functional composition:
`g*h` first applies `h`, then `g`, so its quasi-isogeny is
`(quasiIsogeny c h).trans (quasiIsogeny c g)`. For a central scalar matrix,
`quasiIsogeny_scalar_hom` identifies its forward rational map with the actual
scalar multiple of the identity, using preservation of the algebra scalar map.

For a height-certified fixed frame and an actual framed representative `X`,
`matrixSourceQuasiIsogeny` extends both actual inverse rational maps along
`X.residueMap` and restricts them to exactly the original reduced target cover
used by `X.source`. It proves the actual whole source identity, multiplication
and inverse equations by the existing preservation laws for coefficient
extension and global atlas restriction. It does not detect equality of global
rational maps using charts or points.

The provenance is internal: all constructions follow from a chosen actual
algebra equivalence, actual rational composition and inverse equations, and
actual coefficient extension and restriction. This is the matrix-source part
needed for the later Drinfeld action. It proves no determinant/height law,
Frobenius comparison, preservation of framing height zero under arbitrary
matrices, or full `GL(d,K) × Dˣ` action. The source-specific residue field,
invariant-`1/d` division algebra, existence of matrix coordinates and full
Frobenius correction remain further obligations.
