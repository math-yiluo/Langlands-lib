# Well-definedness of the assembly

`Langlands/Correspondence/AssemblyWellDefinedProof.lean` proves the Library statement
`Langlands.Correspondence.AssemblyWellDefinedStatement` (in
`Langlands/Correspondence/AssemblyRelation.lean`) without extra hypotheses:

```
theorem Langlands.Correspondence.assemblyWellDefined :
    AssemblyWellDefinedStatement.{uF, uP, uA} F
```

Here `p` is a prime and `F : PadicField.{uF} p`. Take any supercuspidal map `c0`
(no correspondence hypothesis on it), any rank `n` and any Weil–Deligne parameter
class `D` of rank `n`. Then exactly one automorphic class `π` of rank `n`
satisfies `IsAssembledFrom F c0 D π`. In words: `D` is a block sum
`⊕_i σ_i ⊗ Sp(m_i + 1)` of uncentered special blocks on irreducible Weil classes,
and `π` is the class of the Langlands head of the multisegment of the segments
`[c0 σ_i, ν^(m_i) c0 σ_i]`.

## Provenance

This is an internal derived result. It follows Henniart 2002, §2.9 (printed
p.596), where the map `π` is defined. That map is well defined by §2.2 (a parameter
is determined by its multiset of indecomposable blocks) and §2.8 (the class of
`J(π_1, …, π_r)` does not depend on an admissible ordering). Every step uses published Library theorems. The proof introduces no
new hypotheses and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The theorem combines existence (`AssemblyWellDefined.exists_isAssembledFrom`) with
the published uniqueness theorem `isAssembledFrom_unique`
(`Correspondence/AssemblyUniqueness`). That theorem shows that two classes
assembled from the same `D` by the same `c0` are equal. It covers independence of
the block decomposition, of the order of the blocks, and of the chosen Langlands
head. Existence has three steps.

### 1. Block decomposition (`exists_isBlockSum`)

Choose a representative `A` of `D`. It is a Frobenius-semisimple parameter.
`localInertia F` is by definition the kernel of `localDegree F`, so that kernel
is compact (`Weil.Local.localInertia_isCompact`). The degree map is surjective
(`Weil.Local.localDegree_surjective`). The published decomposition theorem
`WeilDeligneRepresentation.Blocks.decompositionExistence` holds. So
`WeilDeligneRepresentation.ParameterNormalForm.exists_blocks` gives block data
`b_0, …, b_{k-1}` and an equivalence from `A` to `⊕_i (b_i).pair ν`. Here
`ν = localNormCharacter F`. Each `b_i` has an irreducible Weil representation
whose inertia kernel is open.

An open inertia kernel makes a local Weil representation continuous: this is the
third equivalence of the published `Weil.Local.localWeilContinuity`. So each Weil
factor `B_i` is continuous and irreducible. Being irreducible, it is nontrivial,
so its rank is positive (`rank_pos_of_isIrreducible`). Its class is therefore an
irreducible Weil class in rank `(rank B_i - 1) + 1`
(`irreducibleClassOf`), and `B_i` represents that class by definition
(`weilClassForget_irreducibleClassOf`). Put `d_i = rank B_i - 1` and
`m_i = length b_i - 1`. Then `m_i + 1 = length b_i`, so the published block
`block ν B_i (m_i + 1)` is `(b_i).pair ν`. The inverse of the normal-form
equivalence gives the equivalence `⊕_i block ν B_i (m_i + 1) ≃ A` that
`IsBlockSum F σ m D` requires.

### 2. A Langlands head (`exists_isLanglandsHead`)

The classification theorems are stated for multisegments with carriers in
`max uF uV`. So lift `multisegmentOf F c0 σ m` with
`Multisegment.universeLift`, which keeps the degree
(`Multisegment.universeLift_degree`). For the lifted multisegment `b`:

- `Classification.multisegmentConstituentDataExistence` gives a precedence-ordered
  segment product datum `d` with multisegment `b` and segment heads;
- `Classification.orderedMultisegmentHeadExistence` gives a representation `J` of
  `GL_{deg b}(F)`, with carriers in `max uF uA`, that is the Langlands head of `d`.

So `J` is a Langlands head of `b` (`Multisegment.IsLanglandsHead`).
`Multisegment.isLanglandsHead_universeLift_iff` turns this back into a head of
the original multisegment. Its degree is
`∑_i (d_i + 1)(m_i + 1)` (`degree_multisegmentOf`), which equals `n` by
`IsBlockSum.rank_eq`. So `J` is a representation of `GL_n(F)`.

### 3. An automorphic object (`exists_automorphicObject`)

A Langlands head is irreducible: this is the first component of
`Classification.IsIrreducibleHead`. By
`padicIrreducibleSmoothSmallRealization.{uF, max uF uA, uA}`, `J` is equivalent to
an irreducible smooth representation `τ` with carriers in `uA`. An irreducible
representation has finite length (`SmoothRep.hasFiniteLength_of_isIrreducible`).
By `glFiniteLengthAdmissibility`, finite-length smooth representations of
`GL_n(F)` are admissible, so `τ` is admissible. Hence `τ` is an
`AutomorphicObject.{uF, uA} F n`, and its representation is equivalent to that
of `J`.

### Conclusion

`exists_isAssembledFrom` combines the three steps. The class
`automorphicClassOf F τ` satisfies `IsMultisegmentHeadClass F c0 σ m`: the witnesses
are the object `τ`, the head `J` and the equivalence. With the block decomposition
of step 1, this gives `IsAssembledFrom F c0 D (automorphicClassOf F τ)`.
`isAssembledFrom_unique` then gives uniqueness.
