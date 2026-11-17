# Proof: tempered complex standard modules are irreducible

Lean module: `Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof`.
Worker 728 wrote it under Task 7064 as a supporting proof of the Library statement
`ComplexTemperedStandardIrreducibleStatement` (the target of Task 7113). The operator assigned
this work to Task 7064 in the answer to request `6f5a21aad63b5328a7798c7b491d09e4`.

## Statement proved

`Langlands.Archimedean.complexTemperedStandardIrreducible : ComplexTemperedStandardIrreducibleStatement`
(Library module `ComplexTemperedIrreducibleStatement`). For every `n` and every list `ds` of `n`
complex characters whose exponents all have the same real part, the `(𝔤𝔩_n(ℂ), U(n))`-module
`(complexStandardRep n ds, complexStandardLie n ds)` of `U(n)`-finite functions of
`complexStandardModule n ds` is irreducible (`IsIrreducibleGKModule`).

Notation: a `ComplexCharacterData` `d` is the character `χ_d(z) = (z/|z|)^l |z|^{2t}` with
weight `l = d.weight` and exponent `t = d.exponent`.

## Route

The proof follows Duflo's minimal `K`-type argument (M. Duflo, *Représentations irréductibles des
groupes semi-simples complexes*, LNM 497 (1975), ch. IV, §1.3–1.5; source key
`duflo-1975-representations-irreductibles-complexes`). Its route differs from Badulescu–Renard,
who cite the theory of R-groups. Writing the characters as `z^{l_i} · (weight-0 character)`, a
`U(n)`-fixed vector `T` of the weight-0 standard module times a minor monomial is a vector `f₀`
of the lowest `K`-type. `f₀` is cyclic if `T` is, and lowest `K`-type multiplicity one turns
cyclicity of `f₀` into irreducibility.

## Proof

**Untwisting** (`untwistOne`, `untwist`). For a character `d` of weight `l` and exponent `t`,
`untwistOne d = characterOfParams 0 (t - l/2)` is the character `z ↦ |z|^{2t - l}` of weight `0`.
`character_untwistOne`: `χ_d(z) = z^l · χ_{untwistOne d}(z)`. `positionCharacter_untwist`: the
`i`-th position character of `ds` equals `z^{l_i}` times the `i`-th position character of
`untwist ds`, where `l_i = complexPositionWeight ds i` (`positionWeight_eq`: this is the weight of
`ds[i]`).

**Minor weights** (`exists_minorWeight_eq`). If `w 0 ≤ w 1 ≤ ⋯ ≤ w (n-1)`, then
`w i = ComplexMinorProduct.minorWeight c d i` for `d = w 0` and
`c j = (w (n-1-j) - w (n-2-j)).toNat` (so `c (n-1) = 0`). Here
`minorWeight c d i = d + ∑_{j : n - (j+1) ≤ i} c j`. The proof is induction on `i`: the index
set for `i + 1` is that for `i` plus the single index `n - 2 - i` (`filter_succ`,
`not_mem_filter`), and for `i = 0` it is `{n - 1}` (`filter_zero`).

**Sorted case** (`irreducible_of_sorted`). Assume `TemperedIrreducibleAt b` for all `b < n`
(`ComplexBlockFunctionalSized.TemperedIrreducibleAt b` is the statement for lists of length `b`).
Let `ds` have length `n`, exponents with equal real parts and nondecreasing weights
(`ds.Pairwise (·.weight ≤ ·.weight)`). Put `ds' = untwist ds`; all its weights are `0`.

1. By `exists_minorWeight_eq` there are `c`, `d` with `l_i = minorWeight c d i`. Then the position
   characters satisfy `χ_i(z) = z^{minorWeight c d i} · χ'_i(z)`, which is the hypothesis of
   `complexMinorProductCyclic`.
2. `ComplexSphericalLieGroup.exists_spherical` gives a `U(n)`-fixed `T` in the `U(n)`-finite
   functions of the standard module of `ds'` with `T(1) = 1`. Then `T(κ) = 1` for every `κ ∈ U(n)`
   (`complexStandardRep_apply_apply`), and `T ≠ 0`.
3. `T` is cyclic: every submodule `W` stable under `U(n)` and `𝔤` and containing `T` is `⊤`.
   The exponents of `ds'` are `t_i - l_i/2`.
   * If all weights of `ds` are equal, these exponents have equal real parts, and
     `SphericalCyclic.fixed_cyclic` (the tempered spherical case, module `SphericalCyclic`)
     applies.
   * Otherwise their real parts are nonincreasing along the list (because `Re t_i` is constant
     and `l_i` nondecreasing) and not all equal (two different weights give different real
     parts). `complexSphericalFaceCyclic` (module `ComplexSphericalFace`) applies. Its hypotheses
     include `TemperedIrreducibleAt b` for `b < n`, which is the induction hypothesis.
4. `complexMinorProductCyclic` (module `ComplexMinorProductCyclic`) gives a cyclic `f₀` in the
   `U(n)`-finite functions of the standard module of `ds` with
   `f₀(g) = minorMonomial c d (g) · T(g)`. On `U(n)` this is `minorMonomial c d (κ)`, since
   `T(κ) = 1`.
5. `f₀ ≠ 0`, because the minor monomial does not vanish at the permutation matrix `revUnitary n`
   (`ComplexMinorProduct.minorMonomial_revUnitary_ne_zero`).
6. `complexTemperedIrreducible_of_minorMonomial` (Library module `ComplexLowestKTypeMultOne`:
   lowest `K`-type multiplicity one plus the cyclic-vector criterion) concludes.

**Induction** (`temperedIrreducibleAt`). Strong induction on `n`. Given `ds` of length `n` with
equal real parts, sort it by weight with `List.mergeSort` (`List.pairwise_mergeSort`). The sorted
list `ds'` is a permutation of `ds`, has length `n` and equal real parts. Its characters are
pairwise unlinked, by `ComplexTemperedSorted.isComplexUnlinked_of_re_eq` (equal real parts exclude
linking). The sorted case gives irreducibility for `ds'`, and
`complexStandardIrreducible_of_perm` (Library module `ComplexTemperedSortedReduction`, built on
the swap theorem from `complexGLTwoUnlinkedIrreducible`) transports it to `ds`.

`complexTemperedStandardIrreducible` is `temperedIrreducibleAt n` for each `n`.

## Dependencies

Besides the Library, the proof imports:

* `ComplexMinorProductCyclic` (with `ComplexMinorMonomialCalculus`): the product lemma;
* `ComplexSphericalFace` (with `ComplexSphericalJacquet`): the non-tempered spherical case;
* `SphericalCyclic` (with `SphericalKernel`, `LowerVermaSimple`, `BGChaseWeighted` and
  `ComplexSphericalLieGroup`): the tempered spherical case, including `exists_spherical`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
