# The scalar commutant in the separated discrete-series case, for sorted data

Lean module: `Langlands.Representation.Archimedean.RealDiscreteSeparatedCore`. Author: Worker
380, for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), as part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteSeparated`.

## Purpose and provenance

The module proves no statement of record. Its main theorem `hasScalarCommutant_tgtList` proves
the scalar commutant for the standard module of `tgtList cs Ds = cs, D_d, …, D_1` under the
hypotheses `IsSepData` below and one more hypothesis: Worker 48's
`RealSphericalCyclicStatement` (Library, module `RealSphericalCyclic`; cyclicity of a nonzero
`O(n)`-fixed vector of an even, Langlands-ordered principal series under the Lie algebra). All
declarations are internal. The proof assembles the earlier modules of the chain:

1. the presentation `srcChars cs Ds ↠ tgtList cs Ds` (module `RealDiscretePresentation`);
2. the source as a twist of the even list `midList cs Ds` by the minors with rows `rowSet`
   (module `RealDiscreteSeparatedSource`);
3. a Lie-cyclic `O(n)`-fixed vector of `midList cs Ds`, obtained from spherical cyclicity of
   the sorted list and the sorting surjection (module `RealDiscreteShiftSort`);
4. the frame relations (module `RealDiscreteSeparatedRelations`) in the scalar step
   `hasScalarCommutant_of_frame` (module `RealDiscreteFrame`).

## The hypotheses `IsSepData r cs Ds`

A structure with the fields:

* `re_c`, `re_D`: every character of `cs` and every block of `Ds` has real exponent `r`;
* `sortC`: the even characters of `cs` come before the odd ones;
* `sortD`: `Ds` is sorted by decreasing absolute weight;
* `pos`: every block of `Ds` has nonzero weight;
* `sepC`: no character of `cs` has the (complex) exponent of a block of `Ds`;
* `sepD`: blocks of `Ds` with equal exponents have equal absolute weights.

## Declarations

* `im_ne_of_ne`, `bExp_re`, `bExp_im`, `aExp_re`, `aExp_im`: the exponents
  `t ∓ |m|/2` of the characters `x(D)`, `y(D)` have real parts `Re t ∓ |m|/2` and imaginary part
  `Im t`. `IsSepData.eq_of_im`, `IsSepData.im_ne`: under `IsSepData`, exponents of blocks with
  equal imaginary parts are equal, and a character and a block have different imaginary parts.
* `datumExponent_of_mem_induced`: the Mœglin data of an induction block have its exponent.
* `unlinked_x_c`: `x(D)` is unlinked with every character of `cs` (different imaginary parts,
  `unlinked_of_im_ne`).
* `unlinked_x_D`: `x(D)` is unlinked with every block `E` of `Ds`. If `D` and `E` have different
  exponents, they have different imaginary parts (`unlinked_of_block_im_ne`). If they have the
  same exponent, then `|m_D| = |m_E|` (`sepD`). The datum of `x(D)` is the character
  `(1, t − ℓ/2, triv)` and that of `E` is `(2, t, D_ℓ)`. Mœglin's condition would need
  `t − (t − ℓ/2) = ±(k + ℓ/2)` with `k ≥ 1`, that is `k = 0` or `ℓ + k = 0`; both are impossible.
* `hasGKSurjection_tgtList` (**the presentation**): `hasGKSurjection_chain` with `M = cs`, using
  `unlinked_x_c` and `unlinked_x_D`.
* `eq_charData_of_mem_midList`: every entry of `midList` is an even character `charData 0 t`.
* `pairwise_midList`: if an entry `c` of `midList` precedes an entry `b` and `Re c < Re b`, then
  `Im c ≠ Im b`. The real parts are `r − ℓ_D/2` (`x`-row of `D`), `r` or `r − 1` (even or odd
  character), and `r − ℓ_E/2 − 1` (`y`-row of `E`). Case analysis:
  - two `x`-rows, or two `y`-rows: equal imaginary parts give equal exponents (`eq_of_im`),
    hence equal absolute weights (`sepD`) and equal real parts;
  - two characters: even characters come first (`sortC`), so `Re c ≥ Re b`;
  - an `x`-row and a character: the imaginary parts differ (`im_ne`);
  - an `x`-row of `D` and a `y`-row of `E`: equal imaginary parts give `ℓ_D = ℓ_E`, and then
    `r − ℓ/2 > r − ℓ/2 − 1`;
  - a character and a `y`-row: `r − 1 > r − ℓ_E/2 − 1` since `ℓ_E ≥ 1`.
* `sphList_sorted`: for a list of even characters, the Library spherical list `sphList` of
  `RealTiedMinorProduct` with empty sign set is the list itself.
* `exists_cyclic`: given spherical cyclicity, `midList cs Ds` has an `O(n)`-fixed vector that
  generates it under the Lie algebra. Proof: sort `midList` by decreasing real exponent
  (`insertionSort LangRel`); the sorted list is Langlands ordered and even, so Worker 379's
  spherical vector `sphVec ∅` (Library `RealTiedMinorProduct`, fixed by `O(n)` and nonzero) is
  Lie-cyclic by `RealSphericalCyclicStatement`. By `pairwise_midList` and `unlinked_of_im_ne`,
  `hasGKSurjection_insertionSort` maps the sorted list onto `midList`, and `cyclic_map`
  transports the cyclic fixed vector.
* `bound Ds = max(|m| + 1)` over the blocks (at least `1`), with `one_le_bound`, `le_bound`.
* `hasScalarCommutant_tgtList` (**the separated case for sorted data**): if
  `RealSphericalCyclicStatement`, `IsSepData r cs Ds` and `2|Ds| + |cs| = n`, then
  `HasScalarCommutant n (tgtList cs Ds)`. Proof: with `N = bound Ds`, combine
  `hasGKSurjection_tgtList`, `isMinorShift_src` and `shiftList_eq_midList`, `exists_cyclic`,
  `frameU_mul_frameV` and `exists_frame_rel` in `hasScalarCommutant_of_frame`.
