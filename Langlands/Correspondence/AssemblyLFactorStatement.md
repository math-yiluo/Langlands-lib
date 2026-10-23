# L-factors of the assembled correspondence

Author: Worker 7. This module states two results of Henniart 2002 about the
assembly of a supercuspidal correspondence (`AssemblyRelation`) and pair
L-factors (`FullLFactorCompatibility`):

- the assembly inherits pair L-factor compatibility (Theorem 1.5(iii), L
  part);
- the assembly is the only full map that extends the supercuspidal
  correspondence and has the right pair L-factors against indecomposable
  parameters of smaller rank (Theorem 1.8).

Both are propositions only: nothing is proved, and no correspondence is an
input.

## Definitions

`F : PadicField p` is fixed. Parameter classes are the Frobenius-semisimple
Weil–Deligne classes `WeilDeligneClass F n` of `Domains`, which is
Henniart's `G(n)`.

- `IsIndecomposableParameterClass F D`: some representative of the
  Weil–Deligne class underlying `D` (`parameterForget F D`) is indecomposable
  in the sense of the published `WeilDeligneRepresentation.Blocks.IsIndecomposable`.
  That is, its carrier is nonzero and it has no decomposition into two nonzero
  complementary subspaces stable under the Weil group and the monodromy.
  The classes with this property form Henniart's `G_2(n)`.
- `IsIrreducibleWeilParameter F D`: `D` is the zero-monodromy class of some
  continuous irreducible Weil class `σ` (the published `IsZeroMonodromyOf`
  of `Domains`). These classes form the image of Henniart's `G_0(n)` in
  `G(n)`.

## Statements

- `AssemblyLInheritanceStatement F`: for every supercuspidal map `c0` and
  full map `c`, if `c0` is a supercuspidal correspondence
  (`IsSupercuspidalCorrespondence F c0`) and `c` is an assembly of `c0`
  (`IsAssemblyOf F c0 c`), then `FullPairLCompatibility F c`. That is, for
  every nontrivial `ψ` and all parameter classes `D`, `D'` of any ranks,
  `L(s, c(D) × c(D')) = L(s, D ⊗ D')`.
- `AssemblyLCharacterizationStatement F`: let `c0` be a supercuspidal
  correspondence, `τ` a full map and `ψ` a nontrivial additive character.
  Assume:
  1. `ExtendsSupercuspidal F c0 τ`: on the zero-monodromy class of every
     irreducible Weil class `σ`, `τ` takes the value `c0 σ`; and
  2. for all `j < k`, every parameter class `D` of rank `k + 1` with
     `¬ IsIrreducibleWeilParameter F D`, and every parameter class `D'` of
     rank `j + 1` with `IsIndecomposableParameterClass F D'`,
     `IsPairLCompatibleAt F ψ D D' (τ D) (τ D')`.

  Then `IsAssemblyOf F c0 τ`, and every full map `c` with
  `IsAssemblyOf F c0 c` equals `τ`.

## Sources and provenance

- Henniart 2002, §1.1, printed p.588 (PDF p.2): `G(n)` is the set of classes
  of `n`-dimensional Φ-semisimple representations of `W'_F`, and `G_0(n)` the
  subset of irreducible representations of `W_F`. §1.7, printed p.591
  (PDF p.5): `G_2(n)` is the set of classes of indecomposable
  representations of `W'_F`.
- Henniart 2002, §1.3, printed p.589 (PDF p.3): the supercuspidal family
  `π^0_n` exists, is compatible with contragredients and with pair epsilon
  factors, and is bijective. §1.4, printed p.589: this family is unique.
- Henniart 2002, §1.5, printed p.590 (PDF p.4), Theorem: the bijections
  `π_n : G(n) → A(n)` built from `π^0` (§2) satisfy (i) `π_n = π^0_n` on
  `G_0(n)`, (ii) compatibility with contragredients on `G_0(n)`, and (iii)
  `L(s, π_n(σ) × π_n'(σ')) = L(s, σ ⊗ σ')` and the corresponding epsilon
  identity, for all `n, n' ≥ 1`, `σ ∈ G(n)` and `σ' ∈ G(n')`.
  `AssemblyLInheritanceStatement` is the L identity of (iii). The proof is
  in §2.8–§2.9, printed p.596 (PDF p.10): the factors of a Langlands
  quotient are the products of the factors of its essentially
  square-integrable components, and `π` is built from `π_2` through the
  identifications `N[G_2] - {0} = G` and `N[A_2] - {0} = A`.
- Henniart 2002, §1.8, printed p.591 (PDF p.5), Theorem: let `(τ_n)` be maps
  `G(n) → A(n)` with (i) `τ_n(σ) = π^0_n(σ)` for `σ ∈ G_0(n)`, `n ≥ 1`, and
  (ii) `L(s, τ_n(σ) × τ_r(τ)) = L(s, σ ⊗ τ)` for `1 ≤ r < n`,
  `σ ∈ G(n) - G_0(n)` and `τ ∈ G_2(r)`. Then `τ_n = π_n` for every
  `n ≥ 1`. `AssemblyLCharacterizationStatement` is this theorem, with
  `n = k + 1` and `r = j + 1`, so `1 ≤ r < n` becomes `j < k`.
- Henniart 2002, §4.5, printed p.600 (PDF p.14): the proof, by induction on
  `n` from Theorems 1.5 and 1.7. When it restates hypothesis (ii) it writes
  `τ ∈ G(r)`, and `⊗` where §1.8 has `×`. The argument uses (ii) only for
  `τ ∈ G_2(r)`. The module follows the statement of §1.8.

Source file: `henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Interpretation

- **The supercuspidal family.** Henniart's `π^0` is the family of his
  Theorem 1.3. Here `c0` is any map with `IsSupercuspidalCorrespondence F c0`
  (`SupercuspidalSpecification`). That predicate contains the conditions of
  Theorem 1.3 and the further conditions of Henniart 2000, §§1.2–1.3:
  bijectivity, contragredients, rank one, determinants, twists, and pair L-
  and epsilon factors for every nontrivial `ψ`. By the uniqueness of §1.4 the
  two descriptions give the same family, but the module does not use that
  uniqueness. Both statements hold for every such `c0`.
- **`π_n` is the assembly.** Henniart's `π_n` is the map built from `π^0` in
  §2.9. Here it is the relation `IsAssemblyOf F c0` of `AssemblyRelation`.
  "`τ_n = π_n` for all `n`" becomes: `τ` is an assembly of `c0`, and every
  assembly of `c0` equals `τ`. The second conjunct also follows from the
  first and the published, unproved `AssemblyWellDefinedStatement`. It is
  included so that the conclusion says that `τ` is *the* assembly without
  relying on that statement.
- **One additive character.** Henniart fixes one nontrivial `ψ` (§1.1), and
  hypothesis (ii) of Theorem 1.8 involves only L-factors, which do not depend
  on `ψ`. The published representation-side L relation is stated at a `ψ`
  and a measure (`FullLFactorCompatibility`). So the hypothesis is required
  at one arbitrary `ψ` and not at all of them, which gives the stronger
  theorem. Hypothesis 2 also contains the existence of a measure self-dual
  for `ψ`, a true fact that `IsPairLCompatibleAt` asserts so that its
  `∀ ν` clause is not vacuous.
- **Totality.** Hypothesis 2 asserts that the JPSS L-polynomials of the
  pairs `(τ D, τ D')` exist. The conclusion of
  `AssemblyLInheritanceStatement` asserts this for all image pairs.
- **No epsilon factors.** Theorem 1.8 uses only L-factors. Henniart's
  Corollaries 1.6 and 1.8, which characterize the full family by L and
  epsilon factors of pairs, and the epsilon part of Theorem 1.5(iii), need
  the epsilon factor of nongeneric pairs. They are not stated here; see
  Scope.

## Scope

- This module's inheritance and characterization goals remain L-only and
  unproved. The nongeneric epsilon product of Henniart 2002, §2.8, is
  implemented in `RankinSelberg/LanglandsFactors`, with actual quotient-data
  witnesses, block-factor existence and datum independence required by its
  constructor. The published `FullFactorCompatibility` supplies the epsilon
  condition on actual automorphic classes and combines it with full L
  compatibility; `FullSpecification` supplies `IsFullCorrespondence` and
  unproved existence and uniqueness goals (see `FullLFactorCompatibility`,
  Scope).
- The epsilon part of Theorem 1.5(iii) is the separate, unproved
  `AssemblyEpsilonInheritanceStatement` in `AssemblyTheorems`: a
  supercuspidal correspondence and its assembly satisfy
  `FullEpsilonCompatibility` for each geometrically normalized reciprocity
  candidate. The same module's `ConditionalAssemblyStatement` says that,
  given a supercuspidal correspondence, an assembly exists and every
  assembly is a full correspondence. Both declarations are `Prop` targets,
  not proofs. Their availability does not assert formalization or proof of
  every corollary mentioned above, or unconditional analytic existence,
  classification or descent.
- Theorems 1.6, 1.7 and 1.9 characterize classes on one side only (the
  parameter side or the representation side); they are not statements of
  this task.
- The module imports, and does not copy: this task's
  `FullLFactorCompatibility` (`IsPairLCompatibleAt`,
  `FullPairLCompatibility`), `AssemblyRelation` (`IsAssemblyOf`),
  `SupercuspidalSpecification` (`IsSupercuspidalCorrespondence`) and
  `Domains` (`IsZeroMonodromyOf`, `ExtendsSupercuspidal`), and the published
  `WeilDeligne/BlockStatements` (`Blocks.IsIndecomposable`).
- This candidate also changes `AssemblyRelation.lean`. Its two local
  topology instances now have explicit names (`assemblyFieldTopology`,
  `assemblyGeneralLinearTopology`). Before, `AssemblyRelation` and
  `ArithmeticFactors` both received the automatic name
  `instTopologicalSpaceCarrier_4`, so no module could import both. No other
  declaration of `AssemblyRelation` changes, and its Markdown does not
  mention the instances.

## Validation

The module compiles in the project Lean service, together with
`FullLFactorCompatibility` and the edited `AssemblyRelation`, with no errors
or warnings. There is no `sorry` and no new axiom. Every definition returns
`Prop`; the inspection of `AssemblyLCharacterizationStatement` reports
`statement_returns_prop`.
