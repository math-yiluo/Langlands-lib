# Every assembly of a supercuspidal map extends it

This module proves the published proposition
`Langlands.Correspondence.AssemblyExtendsStatement` (module `AssemblyRelation`):

```lean
theorem Langlands.Correspondence.assemblyExtends :
    AssemblyExtendsStatement.{uF, uP, uA} F
```

Here `p` is any prime (`[Fact p.Prime]`) and `F : PadicField.{uF} p` is any p-adic
field. These come from the section variables. The universe levels `uF` (field),
`uP` (parameter carriers) and `uA` (representation carriers) are arbitrary and
independent. The theorem has no further hypotheses. In particular it does not assume
that the assembly is well defined, and it assumes nothing about `c0` or `c` beyond
the hypothesis `IsAssemblyOf F c0 c` of the statement. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Let `c0` be a supercuspidal map over `F`, that is, for each rank `n` a map from
irreducible Weil classes of rank `n` to supercuspidal classes of `GL_n(F)`. Let `c`
be a full map, from Frobenius-semisimple Weil–Deligne parameter classes of rank `n` to
irreducible classes of `GL_n(F)`. Assume `c` is an assembly of `c0`
(`IsAssemblyOf F c0 c`). This means: for every rank `n` and every parameter class
`D`, the class `c n D` is the Langlands head of the multisegment of some block
decomposition `D = ⊕_i σ_i ⊗ Sp(m_i + 1)`. The conclusion is the published
`ExtendsSupercuspidal F c0 c`. For every rank `n` and every irreducible Weil class
`σ` of rank `n` there is a parameter class `D` such that:

- `IsZeroMonodromyOf F σ D` holds, so `D` is the class of `σ` with zero monodromy;
- `c n D = supercuspidalToAutomorphic F (c0 n σ)`, so `c` sends `D` to the
  supercuspidal class `c0 n σ`, viewed as an irreducible class.

## Literature context

Henniart 2002, *Une caractérisation de la correspondance de Langlands locale pour
GL(n)* (`henniart-2002-characterization`), §2.9, printed p. 596. There the bijection
`π` on all Weil–Deligne classes is built from the supercuspidal bijection `π_0` on
blocks, and Henniart records `π(σ) = π_0(σ)` for irreducible `σ`. An irreducible `σ`
is the single block `σ ⊗ St_1` (§2.3, printed p. 594). The segment `[π_0(σ)]` of
length one has head `π_0(σ)` (§2.6–2.7, printed p. 595). In this project the assembly
is a relation (`IsAssembledFrom`, `IsAssemblyOf`). So the Lean proof is not a
transcription of a printed proof. It combines the Library results below.

## Imported results

| Library result | Module | Content |
| --- | --- | --- |
| `zeroMonodromyParameter F σ` | `Correspondence/IrreducibleZeroMonodromy` | A chosen parameter class of rank `n` for each irreducible Weil class `σ` of rank `n` |
| `zeroMonodromyParameter_spec F σ` | `Correspondence/IrreducibleZeroMonodromy` | `IsZeroMonodromyOf F σ (zeroMonodromyParameter F σ)`: a representative of `σ` with zero monodromy is a Frobenius-semisimple parameter, and its class is that parameter class |
| `isAssembledFrom_of_isZeroMonodromyOf F c0 h` | `Correspondence/AssemblyZeroMonodromyWitness` | If `IsZeroMonodromyOf F σ D`, then `IsAssembledFrom F c0 D (supercuspidalToAutomorphic F (c0 n σ))`. The decomposition has one block, `σ ⊗ Sp(1)` (`r = 1`, `m = 0`), and the multisegment is `{[c0 σ]}` |
| `isAssembledFrom_unique F c0 h h'` | `Correspondence/AssemblyUniqueness` | Two classes assembled from the same parameter class by the same `c0` are equal. No hypothesis; this is the uniqueness half of `AssemblyWellDefinedStatement` |

None of these results has unproved hypotheses. The existence half of
well-definedness (`assemblyWellDefined`, module `AssemblyWellDefinedProof`) is not
used. The witness module also has `assembly_apply_of_isZeroMonodromyOf`, which takes
`AssemblyWellDefinedStatement F` as a hypothesis. It is not used either: the proof
applies `isAssembledFrom_unique` directly, which needs no hypothesis.

## Proof

Let `c0`, `c`, `hc : IsAssemblyOf F c0 c`, a rank `n` and an irreducible Weil class
`σ` of rank `n` be given. Put `D := zeroMonodromyParameter F σ` as the witness.

1. `IsZeroMonodromyOf F σ D` is `zeroMonodromyParameter_spec F σ`.
2. Applying `hc` at rank `n` and class `D` gives
   `IsAssembledFrom F c0 D (c n D)`.
3. Applying `isAssembledFrom_of_isZeroMonodromyOf F c0` to the fact in step 1 gives
   `IsAssembledFrom F c0 D (supercuspidalToAutomorphic F (c0 n σ))`.
4. `isAssembledFrom_unique F c0`, applied to steps 2 and 3, gives
   `c n D = supercuspidalToAutomorphic F (c0 n σ)`.

The pair (step 1, step 4) is the required existential for `ExtendsSupercuspidal F c0 c`.
The Lean proof is this single term.
