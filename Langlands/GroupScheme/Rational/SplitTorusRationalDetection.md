# Rational-point detection for a split torus over an infinite field

This is internal infrastructure for the proof of the published
`Langlands.GroupScheme.NormalizerPointsInfiniteFieldStatement`. It proves the
elementary density step described in that statement's paired Markdown directly
with regular functions. Its proof route uses the existing character-algebra and
split-torus constructions and Mathlib results; it introduces no additional
literature input.

Let `k` be an infinite field in any universe and let `I` be a finite index type.
`eq_zero_of_forall_units_zpow_eq_one` first proves that an integer `d` satisfying
`x ^ d = 1` for every `x : kˣ` is zero. If `d` were nonzero, every nonzero element
of `k` would be a root of `X ^ d.natAbs - 1`. The complement of zero is infinite,
so Mathlib's `Polynomial.eq_zero_of_infinite_isRoot` would make that polynomial
zero, contrary to its coefficient of degree `d.natAbs`.

`rationalMonomial` interprets an exponent vector `I → ℤ` as a multiplicative
character of `I → kˣ` with values in `k`. Distinct vectors give distinct
characters: evaluation on a tuple equal to one outside one coordinate reduces
this to the preceding integer-exponent lemma. Mathlib's
`linearIndependent_monoidHom` then gives linear independence of these
characters. Expanding a Laurent polynomial by
`AddMonoidAlgebra.induction_linear` identifies its evaluations with the
corresponding linear combination. Consequently
`eq_zero_of_evaluateUnits_eq_zero` proves that a Laurent polynomial vanishing
on all unit tuples is zero. This also includes the empty index type.

`RationalPointsDetectFunctions X` says that a global regular function on a
scheme `X` over `Spec k` is zero whenever its pullback to `Spec k` is zero at
every rational point over `k`. This property is invariant under isomorphisms.
For the diagonalizable group with character group `I → ℤ`, rational
evaluations of its coordinate algebra give scheme points by `Spec.map`.
Naturality of `Scheme.ΓSpecIso` identifies their pullbacks with the preceding
Laurent evaluations. The published `Diagonalizable.splitIso`, followed by an
isomorphism witnessing `IsSplitTorus`, therefore proves this property for any
split torus.

The final two lemmas provide the interfaces used by the normalizer proof.

- `IsSplitTorus.hom_ext_kpoints`: two morphisms from a split torus to an affine
  scheme over `k` are equal if their composites with every rational point are
  equal. Apply function detection to the difference of the two pullbacks of
  each global function, then use `ext_of_isAffine`.
- `IsSplitTorus.exists_factor_of_kpoints`: a morphism from a split torus into an
  affine scheme factors through a closed immersion if each rational point
  factors through it. Function detection shows containment of the kernels on
  global sections. `Scheme.ker_of_isAffine` and
  `Scheme.IdealSheafData.le_of_isAffine` turn this into containment of the
  ideal-sheaf kernels. Mathlib's `IsClosedImmersion.lift` constructs the
  factorization, which is a morphism over `k` by its defining triangle.

The targets of the last two lemmas are arbitrary affine schemes over `k`;
they need no group structure. The closed-immersion source need not have a
separate affine hypothesis. All assertions use the infinite-field hypothesis
only through the integer-exponent argument.
