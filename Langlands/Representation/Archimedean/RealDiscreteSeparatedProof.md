# The separated discrete-series case

Lean module: `Langlands.Representation.Archimedean.RealDiscreteSeparatedProof`. The theorems
`realTiedDiscreteSeparated_of_sphericalCyclic` and `realTiedDiscreteSeparatedScalarCommutant`
are in the namespace `Langlands.Archimedean`; the other declarations are in
`Langlands.Archimedean.RealDiscreteSeparated`.

## Purpose and provenance

The module proves

`realTiedDiscreteSeparated_of_sphericalCyclic :
  RealSphericalCyclicStatement → RealTiedDiscreteSeparatedScalarCommutantStatement`

and, with the Library proof `RealSphericalCyclicProof.realSphericalCyclic` of
`RealSphericalCyclicStatement` (module `RealSphericalCyclicProof`), the unconditional

`realTiedDiscreteSeparatedScalarCommutant : RealTiedDiscreteSeparatedScalarCommutantStatement`.

`RealTiedDiscreteSeparatedScalarCommutantStatement` (module
`RealTiedDiscreteScalarCommutantCases`) is the separated discrete-series case of
`RealTemperedScalarCommutantStatement`: for every list `ds` of real blocks of total rank `n`
with equal real exponents, at least one discrete-series block, and separated discrete exponents
(`IsRealDiscreteExponentSeparated`: every block with the complex exponent of a discrete-series
block `x` is an induction block with the absolute weight of `x`), the standard module has a
scalar simultaneous `O(n)`/Lie commutant (`HasScalarCommutant n ds`).
`RealSphericalCyclicStatement` (module `RealSphericalCyclic`) is the hypothesis of the first
theorem; the second theorem discharges it. The proof below does not use the hypothesis that `ds` has a discrete-series block.

All declarations are internal. The module uses only the reductions of the separated case to
sorted data (`RealDiscreteSeparatedCore`) and the Library tools in
`RealTiedScalarAssembly`: `blockChars`, `flatMap_expand_eq`, `exponent_re_of_mem_blockChars`,
`sortParity`, `hasScalarCommutant_perm` (the scalar commutant is invariant under permutations
of lists with equal real exponents) and `hasScalarCommutant_of_twoWay`. The Library lemma
`realStandardModule_append_flatMap_expand` (`RealLinkedJacquetPairReduction`) identifies a
block of weight `0` with its two characters. The proof
uses no Langlands-quotient statement, no tempered-irreducibility statement and no Library result
on tied lists that assumes tempered irreducibility.

## Declarations

* `AbsRel e f := |m_f| ≤ |m_e|`, with decidability, totality and transitivity instances;
  `List.insertionSort AbsRel` sorts induction data by decreasing absolute weight.
* `exists_split`: every `ds` is a permutation of `nd ++ Ds₀.map induced` with no
  discrete-series block in `nd` and only nonzero weights in `Ds₀` (induction on `ds`; a
  discrete-series block goes to the second part via `List.perm_middle`).
* `exponent_of_mem_blockChars`: the characters of a non-discrete block have its complex
  exponent.
* `absWeight_ne_of_not_ds`: a non-discrete block has absolute weight `none` (character) or
  `some 0` (weight-zero induction block), never `some k` with `k > 0`.
* `hasScalarCommutant_of_separated`: if `RealSphericalCyclicStatement` holds, `realRank ds = n`,
  all blocks have the same real exponent `r`, and `ds` has separated discrete exponents, then
  `HasScalarCommutant n ds`.

  Proof. Split `ds` by `exists_split`. Put `cs₀ = nd.flatMap blockChars` (the characters of the
  non-discrete blocks), `cs = sortParity cs₀` (even characters first) and
  `Ds = Ds₀.insertionSort AbsRel`. Then `IsSepData r cs Ds` holds: the real exponents are `r`;
  `sortC`, `sortD` hold by construction; weights are nonzero. For `sepC`, a character `c` of a
  non-discrete block `x` with the exponent of a block `E ∈ Ds` would give, by separation applied
  to the discrete-series block `induced E`, `realBlockAbsWeight x = some |m_E|`, contradicting
  `absWeight_ne_of_not_ds`. For `sepD`, separation applied to `induced E` and `induced F` gives
  `|m_E| = |m_F|`. The ranks give `2|Ds| + |cs| = n`
  (`realRank nd = |cs₀|` by `flatMap_expand_eq` and `realRank_flatMap_expand`). So
  `hasScalarCommutant_tgtList` gives the scalar commutant for
  `tgtList cs Ds = cs.map character ++ Ds.reverse.map induced`. Then:
  1. `hasScalarCommutant_perm` moves it to the permutation `Ds₀.map induced ++ cs₀.map character`;
  2. the standard modules of `Ds₀.map induced ++ nd` and `Ds₀.map induced ++ cs₀.map character`
     are equal (`realStandardModule_append_flatMap_expand` and `flatMap_expand_eq`), so
     `hasScalarCommutant_of_twoWay` with the identity maps moves it to
     `Ds₀.map induced ++ nd`;
  3. `hasScalarCommutant_perm` moves it to `ds`.
* `realTiedDiscreteSeparated_of_sphericalCyclic`: the statement form of
  `hasScalarCommutant_of_separated`.
* `realTiedDiscreteSeparatedScalarCommutant`: the separated case itself, obtained by applying
  `realTiedDiscreteSeparated_of_sphericalCyclic` to `RealSphericalCyclicProof.realSphericalCyclic`.
