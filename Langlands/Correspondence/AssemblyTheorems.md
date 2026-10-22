# The assembled correspondence

Author: Worker 7. This module states two results of Henniart 2002 about the
assembly of a supercuspidal correspondence (`AssemblyRelation`):

- the assembly inherits pair epsilon-factor compatibility (Theorem 1.5(iii),
  epsilon part);
- conditionally on a supercuspidal correspondence, an assembly exists and
  every assembly is a full correspondence (Theorem 1.5 and §2.9).

Both are propositions only: nothing is proved. They separate the three
levels of the classification. The prerequisite is the existence of the
supercuspidal correspondence (`SupercuspidalCorrespondenceStatement` of
`SupercuspidalSpecification`). The conditional assembly theorem is
`ConditionalAssemblyStatement` here. The final unconditional statement is
`FullCorrespondenceStatement` of `FullSpecification`, whose input contains no
correspondence.

## Statements

Fix `F : PadicField p`.

- `AssemblyEpsilonInheritanceStatement F`: for every supercuspidal map `c0`,
  full map `c` and rank-one reciprocity candidate `e`, if
  `IsSupercuspidalCorrespondence F c0`, `IsAssemblyOf F c0 c` and
  `IsGeometricReciprocity F e`, then `FullEpsilonCompatibility F e c`
  (`FullFactorCompatibility`). That is, some local-constant system with base
  reciprocity component `e` gives
  `ε(s, c(D) × c(D'), ψ) = ε(s, D ⊗ D', ψ)` for every nontrivial `ψ` and all
  parameter classes `D`, `D'` of any ranks.
- `ConditionalAssemblyStatement F`: for every supercuspidal map `c0` with
  `IsSupercuspidalCorrespondence F c0`:
  1. some full map `c` satisfies `IsAssemblyOf F c0 c`; and
  2. every full map `c` with `IsAssemblyOf F c0 c` satisfies
     `IsFullCorrespondence F c` (`FullSpecification`).

`IsAssemblyOf F c0 c` is the published relation of `AssemblyRelation`: for
every parameter class `D`, there is a block decomposition
`D = ⊕_i σ_i ⊗ Sp(m_i + 1)` such that `c(D)` is the class of the Langlands
head of the multisegment of the segments of length `m_i + 1` beginning at
`c0 σ_i`.

## Sources and provenance

- Henniart 2002, §1.5, printed p.590 (PDF p.4), Theorem: the bijections
  `π_n : G(n) → A(n)` extending `π^0_n` satisfy (i) `π_n = π^0_n` on
  `G_0(n)`, (ii) compatibility with contragredients on `G_0(n)`, and (iii)
  the pair L- and epsilon identities for all `n, n' ≥ 1`, `σ ∈ G(n)`,
  `σ' ∈ G(n')`. `AssemblyEpsilonInheritanceStatement` is the epsilon identity
  of (iii); the L identity is `AssemblyLInheritanceStatement` of
  `AssemblyLFactorStatement`.
- Henniart 2002, §2.8, printed p.596 (PDF p.10): the epsilon factor of a
  Langlands quotient is the product of the epsilon factors of its essentially
  square-integrable components, with the same `ψ`. §2.9, printed p.596: `π` is
  built from `π_2` through the identifications `N[G_2] - {0} = G` and
  `N[A_2] - {0} = A`, and it satisfies `π(σ) = π^0(σ)` for `σ ∈ G_0`,
  `π(σ^∨) = π(σ)^∨` for `σ ∈ G`, and the L, epsilon and gamma identities for
  `σ, σ' ∈ G`. `ConditionalAssemblyStatement` is this construction and its
  properties, as a statement about every supercuspidal correspondence.
- Harris–Taylor 2001, Introduction, printed pp.1–2 (PDF pp.9–10): the
  properties 1–5 of a local Langlands correspondence, which
  `IsFullCorrespondence` contains. For the assembly, rank one, determinants,
  twists and contragredients are the published `AssemblyOperationStatement`
  of `AssemblyRelation`, bijectivity is `AssemblyBijectiveStatement`, and the
  L identity is `AssemblyLInheritanceStatement`.

Source files:

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

## Interpretation

- **Geometric `e`.** The epsilon inheritance is stated for every
  geometrically normalized `e`. The supercuspidal correspondence `c0` uses
  its own geometrically normalized candidate. The published, unproved
  `LocalClassField.WeilReciprocityExistenceUniqueness` says there is exactly
  one such candidate, so the two agree.
- **Existence of the assembly.** `IsAssemblyOf` is a relation, so the first
  conjunct of `ConditionalAssemblyStatement` asserts that the assembly
  exists. It needs the Weil–Deligne block decomposition, the existence of
  Langlands heads and the published classification statements; their
  statements are in `AssemblyRelation` and the published
  `Representation/Classification/MultisegmentClassificationStatement`.
- **Every assembly.** The second conjunct is required of every assembly, so
  it does not depend on a choice. The published
  `AssemblyWellDefinedStatement` says that every parameter class is assembled
  to exactly one class, so there is at most one assembly.
- **Separation of levels.** `ConditionalAssemblyStatement` takes a
  supercuspidal correspondence as hypothesis. `FullCorrespondenceStatement`
  takes none: its proof is expected to combine
  `SupercuspidalCorrespondenceStatement`, `ConditionalAssemblyStatement` and
  the uniqueness of Henniart 2002, Corollary 1.8
  (`FullCharacterizationStatement`). None of these is assumed by another.

## Scope

- The module imports, and does not copy: this task's `FullSpecification`
  (`IsFullCorrespondence`, and through it `FullFactorCompatibility` and
  `SupercuspidalSpecification`) and `AssemblyRelation` (`IsAssemblyOf`).

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Both definitions return `Prop`.
