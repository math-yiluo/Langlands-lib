# Unipotence from unipotent rational points of a solvable group

Module `Langlands.GroupScheme.Reductive.RadicalFieldExtension.Unipotence`.

This module is an internal step in the proof of
`Langlands.GroupScheme.AlgebraicallyClosedRadicalFieldExtensionStatement`, used by the module
`RationalSide`. Its results are derived facts, a form of the Lie–Kolchin argument for
solvable groups stated for rational points; they are not statements taken from the
literature.

## Statements

- `isClosed_toLin'_linear`: for a matrix representation `σ` of a group scheme `H` over a field
  `K`, a `K`-linear functional `Λ` on endomorphisms of `n → K` and a scalar `c`, the set of
  rational points `x` with `Λ (toLin' (σ.rationalMatrix x)) = c` is closed in the
  `RationalZariski.topology` of rational points.
- `isUnipotent_of_isNilpotent_rationalMatrix`: let `H` be a smooth affine connected group
  scheme over an algebraically closed field `K`. Suppose its group of rational points is
  solvable, `ρ : H → GL_N` is a matrix representation that is a closed immersion, and
  `ρ(h) - 1` is nilpotent for every rational point `h`. Then `H` is unipotent
  (`IsUnipotent H`).

## Proof

This is the standard Lie–Kolchin argument for solvable groups, here applied to rational
points.

1. Every rational point acts unipotently in every representation `σ`. This uses the
   translation lemmas of `Derived/CentralIntersection/Unipotence.lean`. Right translation by
   a rational point `h` acts locally unipotently on the entries of `ρ`'s universal matrix and
   of its inverse, because `ρ(h)` and `ρ(h⁻¹)` are unipotent
   (`mem_locallyUnipotent_of_mapMatrix_eq_mul{,_left}`). Those entries generate the
   coordinate ring, since `ρ` is a closed immersion (`mem_of_isClosedImmersion`). So
   translation is locally unipotent on all of `Γ(H, 𝒪)`, and
   `isNilpotent_sub_one_of_mapMatrix_eq_mul` gives that `σ`'s universal matrix minus one,
   translated, is nilpotent. Evaluating at the identity gives that `σ(h) - 1` is nilpotent.
2. The rational points carry the induced Zariski topology. In it the group is preconnected
   (`RationalZariski.preconnectedSpace`), and left multiplication, inversion and
   commutators are continuous (`RationalZariski.continuous_comp` with
   `exists_comp_eq_mul_left` and `exists_comp_eq_commutator_left`). By
   `isClosed_toLin'_linear`, linear conditions define closed sets. So the abstract
   Lie–Kolchin theorem `Langlands.LieKolchin.exists_common_eigenvector_of_isSolvable` gives
   a nonzero vector `v` that is an eigenvector of `σ(h)` for every rational point `h`.
3. Each eigenvalue equals `1`, because `σ(h) - 1` is nilpotent. So `v` is fixed by every
   rational point. `H` is reduced, being smooth over a field
   (`SmoothReducedProof.isReduced_of_smooth_over_field`), so
   `eq_zero_of_forall_evalPoint_eq_zero` makes `v` fixed by the universal point. Then
   `MatrixRepresentation.isFixedVector_iff_universal` gives the fixed vector that
   `IsUnipotent` requires.
