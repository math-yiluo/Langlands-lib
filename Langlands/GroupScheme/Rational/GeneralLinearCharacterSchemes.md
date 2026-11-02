# Scheme character values on GL matrices

This internal construction supports the GL rational-character classification
associated to Renard (2026), V.2.2, printed p.105, and Waldspurger (2003), I.1,
printed pp.238–239. It is a derived reformulation on affine points, using actual
group-scheme homomorphisms into the published multiplicative group.

`coordinateDiagonalHom` is the published diagonal cocharacter with the weight
one at a specified coordinate and zero elsewhere. Its affine points are
`coordinateDiagonalUnits`. `characterOnAffineMatrices` evaluates an actual
scheme character on the point corresponding to an invertible matrix over a
test algebra and identifies the resulting multiplicative-group point with a
unit of that algebra. Evaluation commutes with every change of test algebra.

If the composite along a coordinate diagonal equals multiplication by an
integer `m` on the multiplicative group, evaluation on that diagonal is the
power `a ^ m`. The proof uses the published point comparisons, their naturality,
and the point formula for integer multiplication.
