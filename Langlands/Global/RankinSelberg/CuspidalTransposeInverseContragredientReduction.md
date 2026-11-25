# Reduction to an actual transpose realization and its intrinsic pairing

This is an internal conditional reduction. It retains
two explicit premises and does not prove
`CuspidalTransposeInverseContragredientStatement`.

All three statement definitions quantify over number fields in an arbitrary
universe `u`, with `CompactSpace (AdeleQuotient F)`, every natural `r`, and every
actual cuspidal operator realization of `GL_(r+1)`.

`CuspidalTransposeRealizationStatement` is the B1 premise. It asks for another
actual cuspidal operator realization `T'` and a complex-linear equivalence
`e : T.Space ≃ₗ[ℂ] T'.Space` satisfying both of the following:

- `IsTransposeIntertwining`, with the actual finite adelic transpose inverse,
  the actual `compactTranspose` on the standard infinite compact, and the actual
  `realLieIota` on the real archimedean Lie algebra;
- equality of the actual continuous adelic functions
  `T'.realization.toContinuous (e x) = transposeDual (T.realization.toContinuous x)`
  for every vector `x`.

`CuspidalTransposePairingStatement` is the B2 premise. It asks for
`HasTransposeContragredientPairing` on the original realization. This requires a
complex-bilinear form invariant with a transpose twist in the second variable,
for all three operator families, whose partial map is a bijection onto all
finite-adelically smooth, infinite-compact-finite contragredient functionals.
No archimedean clause or surjectivity clause is dropped.

`CuspidalTransposeInverseContragredientReductionStatement` is the implication
from these two premises to the exact Library target. The theorem
`cuspidalTransposeInverseContragredientReduction` proves this implication.

The function lemma `cuspFunction_eq_dualFunction_of_transposeDual` first uses the
published comparison of group-scheme and matrix evaluations. By definition,
`dualFunction` evaluates at `w_n` times the transpose inverse. The long Weyl
element is rational, so the original function's rational left invariance removes
it. Thus the continuous-function equality in B1 gives exactly the dual cusp
function in the target. The final reduction takes `e x` as the required vector
of `T'` and uses `IsTransposeIntertwining.isContragredientOf` to transport the
intrinsic B2 pairing to `T × T'`.

The provenance is internal: these definitions isolate the two obligations of
a transpose-realization route, and the proof combines the
existing function comparison, rational invariance, and pairing transport.
Neither B1 nor B2 is established in this module. In particular, the reduction
does not assert a Gelfand--Kazhdan theorem or prove the target.
