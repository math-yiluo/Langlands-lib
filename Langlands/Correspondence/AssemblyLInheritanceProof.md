# Pair L-factor inheritance for the assembled correspondence

Author: Worker 4840.

This module proves `Langlands.Correspondence.AssemblyLInheritanceStatement` with no
extra hypotheses. The theorem `Langlands.Correspondence.assemblyLInheritance` has
exactly the type `AssemblyLInheritanceStatement.{uF, uP, uA} F`. It holds for every
prime `p` with `[Fact p.Prime]` and every `F : PadicField.{uF} p`.

The statement is defined in `AssemblyLFactorStatement`. Take a supercuspidal map
`c0` and a full map `c` with `IsSupercuspidalCorrespondence F c0` and
`IsAssemblyOf F c0 c`. Then `FullPairLCompatibility F c` holds: for every
nontrivial additive character `ψ`, all ranks and all parameter classes `D`, `D'`,
the JPSS pair L-polynomial of the assembled classes `c D` and `c D'` gives the
arithmetic L-factor of `D ⊗ D'`. This is the L part of Henniart 2002,
Theorem 1.5(iii) (printed p.590, PDF p.4), together with §2.8–2.9 (printed p.596,
PDF p.10).

The module only composes published Library theorems. It adds no new mathematics.
The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

All declarations are in namespace `Langlands.Correspondence`.

## The reduction used

`assemblyLInheritance_of_rankinSelberg` (module `AssemblyLParameterPairs`) proves
the target from two representation-side statements, both at universes
`{uF, uA, uA}`:

- `RankinSelberg.SquareIntegrableDataLFactorStatement`: JPSS 1983,
  Theorem (9.5), in product form. The L-factor of a pair of Langlands quotients of
  square-integrable data is the product of the L-factors of the pairs of blocks.
- `RankinSelberg.SegmentHeadLFactorStatement`: Henniart 2002, §2.6. The L-factor
  of a pair of segment heads `St_n(ρ)`, `St_n'(ρ')` is
  `∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`.

That reduction already contains everything else. The parameter side (pair
L-factors multiply over direct sums, and the pair L-factor of two special blocks)
is proved in `AssemblyLParameterPairs`. The universe transport between heads in
`max uF uA` and square-integrable data in `uA` is proved in
`AssemblyLDatumExistence` (`multisegmentHeadDatumExistence`). The supercuspidal
pair-factor compatibility comes from `IsSupercuspidalCorrespondence F c0` inside
the reduction.

This module proves the two statements above and applies the reduction.

## Theorems

### `assemblySegmentHeadLFactor`

```lean
theorem assemblySegmentHeadLFactor :
    RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}
```

Apply `RankinSelberg.segmentHeadLFactor_of_squareIntegrable` (module
`SegmentHeadLFactorReduction`). It needs JPSS 1983, Theorem (8.2)
(`RankinSelberg.SquareIntegrableLFactorStatement`) in both argument orders, at
universes `{uF, uA, uA, max uF uA, max uF uA}`. Both are supplied by
`RankinSelberg.squareIntegrableLFactor` (module `SquareIntegrableLFactorProof`),
which is proved for all universe levels. The two orders coincide here because both
representation universes are `uA`.

### `assemblySquareIntegrableDataLFactor`

```lean
theorem assemblySquareIntegrableDataLFactor :
    RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA}
```

Apply `RankinSelberg.squareIntegrableDataLFactor_of_prerequisites` (module
`SquareIntegrableDataLFactorReduction`) at `uV = uW = uA`. Its six premises are
all published theorems:

- equal-exponent grouping of square-integrable Langlands data, for each argument:
  `Classification.squareIntegrableEqualExponentGrouping` (module
  `SquareIntegrableEqualExponentGroupingProof`), applied at the canonical
  topological data of each field;
- JPSS 1983, Proposition (8.4), for tempered inductions:
  `RankinSelberg.temperedLFactor` (module `TemperedLFactorProof`);
- JPSS 1983, Proposition (9.4), display (3), for standard modules of tempered
  Langlands data: `RankinSelberg.langlandsTypeLFactor` (module
  `LanglandsTypeLFactorProof`);
- uniqueness of ordered tempered Langlands data, for each argument:
  `Langlands.glRegularLanglandsDataUniqueness` (module
  `Classification/RegularLanglandsDataUniquenessProof`).

### `assemblyLInheritance`

```lean
theorem assemblyLInheritance : AssemblyLInheritanceStatement.{uF, uP, uA} F
```

This is `assemblyLInheritance_of_rankinSelberg F` applied to
`assemblySquareIntegrableDataLFactor` and `assemblySegmentHeadLFactor`.

## Provenance

The module is derived. It contains no new literature claim. The target is
Henniart 2002, Theorem 1.5(iii), L part, and §2.8–2.9. The proof follows
Henniart's route: the L-factor of a pair of Langlands quotients is the product
of the L-factors of pairs of segment representations (JPSS (9.5), with
JPSS (8.2) for the segment heads), and this matches the product over pairs of
blocks on the parameter side. Each step is a published Library theorem.
