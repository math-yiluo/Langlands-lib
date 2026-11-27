# Jacquet nonvanishing for a non-maximal level-zero simple type

The theorem in `Langlands.BushnellKutzko.LevelZeroNonmaximalTypeJacquetProof`
has type

```lean
theorem Langlands.BushnellKutzko.levelZeroNonmaximalTypeJacquet :
    Langlands.BushnellKutzko.LevelZeroNonmaximalTypeJacquetStatement.{uF, uρ, uπ}
```

The proof introduces the binders of the proposition and applies
`LevelZero.levelZero_not_subsingleton_jacquet`. For a period `e ≥ 2` and
residue block size `f`, the proof witnesses the conclusion with the block
shape `(f, n - f)` and the matrix whose columns form a basis adapted to the
lattice chain and the supplied bases of its layers. [Statement](LevelZeroNonmaximalTypeJacquetStatement.md)

## Proof

`LevelZeroAdaptedBasis` lifts the layer bases and proves the entrywise
descriptions of the order and its radical. In these coordinates the
representation of the unit group is the inflation of the tensor power of a
finite cuspidal representation. `LevelZeroCuspidalSum` proves vanishing of the
sums over lifted corner unipotents that occur in the compression argument.
[Transport to standard coordinates](LevelZeroSimpleTypeJacquet.md)

Let `K` be the first unit subgroup of the order and compress an operator by
averaging its output over `K`. `LevelZeroSwapStep` uses the cuspidal sums to
prove that compression by an adjacent block transposition kills a type
intertwiner only if the map is zero. `LevelZeroCycle` composes the steps along
the inverse block cycle. `LevelZeroPrincipal` uses a uniformizer-weighted
block cycle that normalizes `K` to deduce injectivity for compression by the
diagonal matrix with a uniformizer in the first block. [Principal lemma](LevelZeroPrincipal.md)

The first block and its complement give an Iwahori factorization of `K` in
`LevelZeroCoarse`. `LevelZeroJacquet` shows that compression by the diagonal
contraction preserves the intertwiner property. If the coinvariants vanished,
a sufficiently large power of this compression would kill the images of a
finite basis of the type space. Injectivity would then force the given nonzero
intertwiner to vanish. The adapted basis transports the resulting nonzero
quotient to the claimed conjugate radical. [Compression criterion](TypeJacquetCompression.md)

## Source

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993). The type data come from (5.5.10)(b), printed p. 185
(PDF p. 197). The first remark of (7.3.2), printed p. 223 (PDF p. 235), deduces
nonvanishing for a non-maximal type. The injectivity argument applies to
smooth representations by (7.3.6)(i), printed p. 225 (PDF p. 237). The Lean
proof uses a two-block parabolic and proves the compression input of (7.3.1),
printed p. 222 (PDF p. 234), by finite residue calculations.

Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
