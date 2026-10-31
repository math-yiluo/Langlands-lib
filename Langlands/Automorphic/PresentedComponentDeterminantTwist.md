# Actual determinant images of presented local components

This internal construction combines `PresentedLocalComponent` with
`FiniteLocalDeterminantTwist`. The number field `F : Type uF` has arbitrary
universe, the matrix rank `n` is any natural number, and coefficients are
complex. The local-factor carriers `V v : Type uV` have an independent
universe and need only their specified complex module structures.

The input is a supplied genuine finite tensor presentation
`P : FiniteTensorPresentation F n ρ E e he S` of an actual finite adelic
invariant form subspace, together with `hS : S ≠ ⊥`. It retains the
existing nonzero reference vectors and integral-fixed reference vectors
outside the finite tensor exceptional set `E`. The multiplier character
`χ` is a continuous finite-order Hecke character.

`determinantTwistLocalComponent` is precisely the actual determinant image
of `P.localComponent hS v`. Thus it uses the existing chosen nonzero
complementary tensor vector and then multiplies each represented adelic
function by `χ(det a)`. Its local action and topology are inherited from
actual automorphic forms. Its nonzeroness follows from the original
component's nonzeroness and injectivity of multiplication.

`determinantTwistLocalComponent_le` places this actual subspace inside
`(S.determinantTwist χ hχ).toLocal F n v`. The proof applies monotonicity
of actual image multiplication to the original component containment,
then uses the equality between multiplication before or after local
restriction.

`determinantTwistLocalComponentEquiv` is a genuine complex-linear
equivariant equivalence from the existing scalar twist
`Langlands.twist (χ.finiteLocalDeterminant n v).toMonoidHom (ρ v)`
onto this image action. It first twists the original faithful local-factor
equivalence and then composes with the actual image's scalar-twist
comparison. The exported application and evaluation formulas identify its
map with actual multiplication on the original represented factor vector.
The character is the actual adelic determinant pullback along the finite
adelic and specified completed-local inclusions, with the positive
right-translation convention and no inverse-character change.

`determinantTwistLocalFactor_isSmooth` proves smoothness of this twisted
specified factor using the injective intertwiner into the actual multiplied
local form subspace. `determinantTwistLocalComponentClass` takes the smooth
class represented in universe `uF`, independently of `uV`.
`determinantTwistLocalComponentClass_eq` compares presentations with the
same tensor data into possibly different nonzero actual finite
realizations. It composes their equivalences with the same twisted local
factor. It asserts equality of smooth classes; no equality of the actual
embedded subspaces is claimed.

At `v ∉ E`, `determinantTwistLocalComponent_exists_integral_fixed` retains
a nonzero vector fixed by the actual integral local subgroup, provided
the actual local determinant character is trivial on that subgroup.
The proof multiplies the original fixed vector, uses injectivity for
nonzeroness, and applies the multiplier's covariance with scalar one.
Triviality on that subgroup is an explicit hypothesis; this module does
not prove it outside a finite set or assert normalized Hecke eigenvalues.

Provenance is internal composition of existing actual slice and
determinant-image constructions and the generic scalar-twist operation.
All intrinsic invariance, containment, equivariance, smoothness and
nonzero obligations above are proved. There is no new original-literature
identification. This module does not construct a tensor presentation of
the twisted global realization, identify a local slice with its entire
local restriction, prove factorization for arbitrary realizations, or
assert Satake, spectral or weak-association compatibility.
