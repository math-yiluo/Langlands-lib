# The split special linear group over a field is simply connected

This internal module proves `SpecialLinear.isSimplyConnected n k`. For a nonempty finite index
type `n` with decidable equality and a field `k`, the split special linear group
`SpecialLinear.groupScheme n (CommRingCat.of k)` is simply connected, in the sense of the
Library's `IsSimplyConnected`. That structure bundles `IsSemisimple` with the condition that
every central isogeny from a semisimple group is an isomorphism. No assumption is made on the
characteristic of `k`.

The proof uses the pivot diagonal torus `diagonalTorus p (CommRingCat.of k)` of rank `|n| - 1`
and the weight description from `Langlands.GroupScheme.SpecialLinearTorus`. Let `𝔻` be its
source `splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (OffPivot p))`, and write
`w = weightCoord p`, so `w(c) = e_c` for `c ≠ p` and `w(p) = -∑_c e_c`. Character and cocharacter
coordinates are the Library's `GeneralLinear.characterCoordEquiv (OffPivot p) k` and
`GeneralLinear.cocharacterCoordEquiv (OffPivot p) k`. Under them, `latticePairing` is the dot
product (`GeneralLinear.latticePairing_coord`).

## A coordinate computation

* `eq_single_of_pairing`: let `ν : I → ℤ` on a finite type `I` and `c : I` satisfy
  `ν_c + ∑_d ν_d = 2` and `ν_d = ν_c - 1` for every `d ≠ c`. Then `ν = e_c` (`Pi.single c 1`).
  Indeed `∑_d ν_d = |I| (ν_c - 1) + 1`, so `(|I| + 1)(ν_c - 1) = 0`. Hence `ν_c = 1`, and the
  other coordinates are `0`.
* `sum_weightCoord_val_mul`: pairing `w(c)` with `ν` gives `ν_c` for `c ≠ p`.
* `sum_weightCoord_pivot_mul`: pairing `w(p)` with `ν` gives `-∑_d ν_d`.

## The zero weight space and maximality

* `mem_weightSpace_zero_iff`: a Lie algebra element lies in the zero weight space exactly when
  its matrix `lieMatrix X` is diagonal. This follows from
  `mem_weightSpace_diagonalTorus_iff_support` and `weightCoord_injective`.
* `zeroWeightCoord p k` (definition): the `k`-linear map from the zero weight space to
  `OffPivot p → k` taking the diagonal entries away from the pivot. `zeroWeightCoord_apply`
  is its formula.
* `apply_pivot_eq_neg_sum`: the pivot diagonal entry of a trace-zero matrix is minus the sum
  of the other diagonal entries.
* `lieMatrix_eq_zero_of_zeroWeightCoord`: an element of the zero weight space with vanishing
  off-pivot diagonal is zero. Its off-diagonal entries vanish because it is diagonal, and its
  pivot entry vanishes by the trace condition (`trace_lieMatrix`).
* `offPivotDiag p d` (definition): the function `n → A` equal to `d c` at `c ≠ p` and to
  `-∑_c d c` at the pivot. `offPivotDiag_val` gives its off-pivot values, and
  `trace_diagonal_offPivotDiag` shows its diagonal matrix has trace zero.
* `zeroWeightCoord_bijective`: `zeroWeightCoord p k` is bijective. Injectivity uses the previous
  lemma and `lieMatrix_injective`. Surjectivity realizes `diag(offPivotDiag p d)` through
  `exists_lieMatrix_eq`.
* `finrank_weightSpace_zero`: the zero weight space has dimension `|OffPivot p| = |n| - 1`.
* `isMaximalTorus_diagonalTorus p k` (**maximality**): the diagonal torus is a maximal torus
  (`IsMaximalTorus`). This is the Library's criterion `isMaximalTorus_of_finrank_zeroWeight`:
  a split closed subtorus whose zero weight space has dimension equal to its rank is maximal.
  The rank of `𝔻` is `|OffPivot p|` by `splitTorus.finrank_lieKernel`.

## Roots

* `exists_coord_of_mem_roots`: every root `χ` of the diagonal torus (the Library's
  `roots (diagonalTorus p (CommRingCat.of k))`) has coordinates `w(x) - w(y)` for some
  `x, y : n`. A nonzero vector in its weight space has a nonzero entry `(x, y)`.
* `coord_mem_of_mem_roots`: every coordinate of a root lies in `[-2, 2]`, since the coordinates
  of `w` lie in `[-1, 1]` (`weightCoord_apply_mem`).
* `rootChar p k x y` (definition): the character of `𝔻` with coordinates `w(x) - w(y)`.
  `characterCoordEquiv_rootChar` gives its coordinates.
* `rootChar_mem_roots`: for `x ≠ y`, `rootChar p k x y` is a root. It is nonzero by
  `weightCoord_injective`, and the trace-zero matrix unit `E_{xy}` gives a nonzero vector in
  its weight space.

## Coroots

* `latticePairing_rootChar`: the pairing of `rootChar p k x y` with a cocharacter `ν`, in
  coordinates.
* `reflection_coord_mem`: let `P` be a root datum of the diagonal torus
  (`IsRootDatumOf (diagonalTorus p (CommRingCat.of k)) P`), let `j` be an index with
  `P.root j = rootChar p k x₀ y₀`, and let `x ≠ y`. Then each coordinate of the reflection
  `(w(x) - w(y)) - ⟨rootChar p k x y, P.coroot j⟩ · (w(x₀) - w(y₀))` lies in `[-2, 2]`. The
  reflection of a root is a root (`P.root_reflectionPerm`, `P.reflection_apply_root`), and the
  pairing of `P` is `latticePairing` (first field of `IsRootDatumOf`).
* `cocharacterCoordEquiv_coroot_of_root_eq_rootChar` (**coroots**): if
  `P.root j = rootChar p k c p` for `c ≠ p` (coordinates `w(c) - w(p) = e_c + ∑_d e_d`), then
  `P.coroot j` has coordinates `e_c`. Write `ν` for its coordinates. The self-pairing
  `P.pairing_same` gives `ν_c + ∑_d ν_d = 2`. For `d ≠ c`, take the reflection bounds for the
  roots `w(d) - w(c)` and `w(d) - w(p)` at coordinate `c`. They give
  `-2 ≤ -1 - (ν_d - ν_c) · 2 ≤ 2` and `-2 ≤ 1 - (ν_d + ∑ ν) · 2 ≤ 2`. With
  `ν_c + ∑ ν = 2`, the integer solutions force `ν_d = ν_c - 1`. Then `eq_single_of_pairing`
  applies.
* `corootSpan_eq_top` (**coroot span**): for every root datum `P` of the diagonal torus,
  `P.corootSpan ℤ = ⊤`. The coroots of the roots `w(c) - w(p)` form the standard basis of the
  cocharacter lattice, transported along `cocharacterCoordEquiv`.

## Simple connectedness

* `exists_rootDatum p k`: the diagonal torus has a reduced root datum. This is the Library's
  `rootDatumExistence` applied to the connected reductive group `groupScheme n (CommRingCat.of k)`
  (`SpecialLinear.isConnectedReductive k n p`) and the split maximal torus
  `diagonalTorus p (CommRingCat.of k)`.
* `isSimplyConnected_of_pivot p k`: `groupScheme n (CommRingCat.of k)` is simply connected.
  Take a root datum `P` from `exists_rootDatum`. The group is semisimple by the Library's
  `splitSemisimpleRootDatum`, because `Y(T) ⧸ P.corootSpan ℤ` is the quotient by `⊤`, hence
  finite. The Library's `splitCorootSpanSimplyConnected` then gives simple connectedness from
  `P.corootSpan ℤ = ⊤`. The pivot only enters the proof. The statement does not mention `p`; it
  needs only some element of `n`.
* `SpecialLinear.isSimplyConnected n k` (**simple connectedness of `SL_n`**): for
  `[Nonempty n]`, `groupScheme n (CommRingCat.of k)` is simply connected. It applies
  `isSimplyConnected_of_pivot` with the pivot `Classical.arbitrary n`.

## Provenance

The simple connectedness of `SL_n` is standard: Milne, *Algebraic Groups* (2017), Example 23.61
(printed p. 502), states that `SL_n`, `Sp_{2n}` and `Spin_n` are simply connected. This module is
internal; the proof is written from the cited Library results and follows the Library's proof
for `Sp_{2n}` (`Langlands.GroupScheme.SymplecticMatrix.SimplyConnected`). It shows that the
coroots of the roots `e_c - e_p` form a basis of the cocharacter lattice of a split maximal torus.
It does not compute the whole root system or the Weyl group.
