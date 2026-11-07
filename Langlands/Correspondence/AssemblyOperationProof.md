# Operation compatibility of the Henniart assembly

Authors: Worker 1715, Worker 1705, Worker 1703.

This module proves the published proposition
`Langlands.Correspondence.AssemblyOperationStatement` (module `AssemblyRelation`):

```lean
theorem Langlands.Correspondence.assemblyOperation :
    AssemblyOperationStatement.{uF, uP, uA} F
```

The statement says the following. Let `c0` be a supercuspidal map, `c` a full map
and `e` a reciprocity candidate, and assume:

- `c` is an assembly of `c0` (`IsAssemblyOf F c0 c`),
- `e` is geometrically normalized (`IsGeometricReciprocity F e`),
- `c0` is compatible with rank one, determinants, twists and duals
  (`SupercuspidalRankOneCompatibility`, `SupercuspidalDeterminantCompatibility`,
  `SupercuspidalTwistCompatibility`, `SupercuspidalDualCompatibility`).

Then `c` satisfies the corresponding four compatibilities: `RankOneCompatibility F e c`,
`DeterminantCompatibility F e c`, `TwistCompatibility F e c` and
`DualCompatibility F c`. The theorem has no further hypotheses. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Literature context

Henniart 2002 (`henniart-2002-characterization`), §2.9 (printed p.596, PDF p.10),
extends the supercuspidal bijection `π_0` to a bijection `π` from all Weil–Deligne
classes to irreducible representations. It lists some properties of `π`: `π(σ) = π_0(σ)`
for irreducible `σ`, which covers rank one, and `π(σ^∨) = π(σ)^∨`. Henniart does not
state the determinant and twist compatibilities there. They are internal derived
results here. In this project the assembly is a relation (`IsAssemblyOf`), so the
argument below is not a transcription of a literature proof. It combines the Library
results listed below.

## Inputs

| Part | Library result | Module |
| --- | --- | --- |
| Rank one | `rankOneCompatibility_of_assembly` | `Correspondence/AssemblyRankOne` |
| Determinant | `AssemblyDeterminant.determinantCompatibility_of_assembly` | `Correspondence/AssemblyDeterminant` |
| Central characters of heads | `Classification.multisegmentConstituentCentralCharacter` | `Representation/Classification/MultisegmentConstituentCentralCharacterProof` |
| Twist of a block sum and of a head class | `AssemblyTwist.exists_isTwistOf`, `AssemblyTwist.isBlockSum_twist`, `AssemblyTwist.isMultisegmentHeadClass_twist` | `Correspondence/AssemblyTwist` |
| Character twists of heads | `Classification.multisegmentConstituentCharacterTwistCompatibility` | `Representation/Classification/MultisegmentConstituentCharacterTwistCompatibilityProof` |
| Dual of a block sum and of a head class | `AssemblyDual.exists_isDualOf`, `AssemblyDual.isBlockSum_dual`, `AssemblyDual.isMultisegmentHeadClass_dual` | `Correspondence/AssemblyDual` |
| Contragredients of heads | `Classification.multisegmentConstituentContragredientCompatibility` | `Representation/Classification/MultisegmentConstituentContragredientProof` |
| Uniqueness of assembled classes | `isAssembledFrom_unique` | `Correspondence/AssemblyUniqueness` (new, in this candidate) |

The modules `AssemblyTwist` and `AssemblyDual` also contain main theorems
`twistCompatibility_of_assembly` and `dualCompatibility_of_assembly`. These assume
the well-definedness of the assembly, `AssemblyWellDefinedStatement`, which is not
proved. Its existence half needs the existence of Langlands heads of multisegments.
The proofs here do not use those two theorems. They repeat their final steps and use
only the uniqueness half, which `isAssembledFrom_unique` proves without hypotheses
(see `AssemblyUniqueness.md`).

## Proof

`assemblyOperation` introduces `c0`, `c`, `e` and the six hypotheses and proves the
four conjuncts.

1. **Rank one.** `rankOneCompatibility_of_assembly` applied to `IsAssemblyOf` and the
   rank-one compatibility of `c0`.
2. **Determinant.** `AssemblyDeterminant.determinantCompatibility_of_assembly`. Its
   hypothesis on central characters of multisegment heads is discharged by
   `Classification.multisegmentConstituentCentralCharacter F F.canonicalTopologicalData`.
   It also uses geometric normalization and the determinant compatibility of `c0`.
3. **Twist** (`twistCompatibility_of_isAssemblyOf`). Fix a rank `n`, a parameter class
   `D` and a quasi-character `χ`. Let `χ_W` be the Weil character
   `LocalFactor.RankOne.weilCharacter F e χ`.
   - `AssemblyTwist.exists_isTwistOf` gives a class `E` with `IsTwistOf χ_W D E`.
     It is the witness parameter class. It remains to show that `c n E` is the twist
     of `c n D` by `χ ∘ det`.
   - `IsAssemblyOf` gives `IsAssembledFrom F c0 D (c n D)`. This is a block sum
     decomposition of `D` with irreducible Weil classes `σ_i` and lengths `m_i + 1`,
     together with the fact that `c n D` is a Langlands-head class of the
     multisegment of `(σ_i, m_i)`.
   - `AssemblyTwist.isMultisegmentHeadClass_twist`, with the character-twist
     compatibility `Classification.multisegmentConstituentCharacterTwistCompatibility`
     and the twist compatibility of `c0`, gives a class `π'`. It is the twist of
     `c n D` by `χ ∘ det` and a Langlands-head class of the twisted Weil classes
     `χ_W ⊗ σ_i` with the same lengths.
   - `AssemblyTwist.isBlockSum_twist` turns the block sum decomposition of `D` into
     one of `E` with the classes `χ_W ⊗ σ_i`. Hence `IsAssembledFrom F c0 E π'`.
   - `IsAssemblyOf` also gives `IsAssembledFrom F c0 E (c n E)`, and
     `isAssembledFrom_unique` gives `c n E = π'`.
4. **Dual** (`dualCompatibility_of_isAssemblyOf`). Fix `n` and `D`. The argument has
   the same structure as the twist case.
   - `AssemblyDual.exists_isDualOf` gives a class `E` with `IsDualOf D E`.
   - `AssemblyDual.isMultisegmentHeadClass_dual` uses the contragredient
     compatibility `Classification.multisegmentConstituentContragredientCompatibility`,
     geometric normalization, and the twist and dual compatibilities of `c0`. It
     gives a class `π'`. This class is the contragredient of `c n D` and a
     Langlands-head class of the classes `ν^(-m_i) σ_i^∨` (`AssemblyDual.dualWeilClass`)
     with the same lengths.
   - `AssemblyDual.isBlockSum_dual` gives a block sum decomposition of `E` with these
     classes, so `IsAssembledFrom F c0 E π'`.
   - `isAssembledFrom_unique` with `IsAssembledFrom F c0 E (c n E)` gives
     `c n E = π'`.

## Declarations

- `twistCompatibility_of_isAssemblyOf`: if `IsAssemblyOf F c0 c` and `c0` is
  compatible with twists, then `TwistCompatibility F e c`.
- `dualCompatibility_of_isAssemblyOf`: if `IsAssemblyOf F c0 c`, `e` is geometrically
  normalized, and `c0` is compatible with twists and duals, then
  `DualCompatibility F c`.
- `assemblyOperation`: the main theorem.

The module `AssemblyUniqueness`, with its own Markdown, belongs to this candidate. It
was adapted with Worker 1703's permission from their unpublished reduction, so
Worker 1703 is a coauthor. The twist and dual steps reuse Worker 1705's reductions.
