# Characterization of the full correspondence by pair factors at one character

Author: Worker 7. This module states two corollaries of Henniart 2002. They
concern a full map `τ` that is compatible with rank one and with all pair L-
and epsilon-factors at one nontrivial additive character:

- `τ` extends the supercuspidal correspondence (Corollary 1.6);
- `τ` is the assembly of the supercuspidal correspondence (Corollary 1.8).

Both are propositions only: nothing is proved, and no correspondence is
asserted to exist.

## Statements

Fix `F : PadicField p`. Both statements quantify over a supercuspidal map
`c0`, a full map `τ`, a nontrivial unitary additive character `ψ` and a
rank-one reciprocity candidate `e`, and assume:

1. `IsSupercuspidalCorrespondence F c0` (`SupercuspidalSpecification`);
2. `IsGeometricReciprocity F e`: `e` is geometrically normalized;
3. `RankOneCompatibility F e τ`: in rank one, `τ` sends the class of `χ ∘ e`
   to `χ`, for every quasi-character `χ` of `F^×`; and
4. `FullFactorCompatibilityAt F e ψ τ` (`FullFactorCompatibility`): for all
   ranks `n, n' ≥ 1` and all parameter classes `D` of rank `n` and `D'` of
   rank `n'`, `L(s, τ(D) × τ(D')) = L(s, D ⊗ D')` at `ψ`, and
   `ε(s, τ(D) × τ(D'), ψ) = ε(s, D ⊗ D', ψ)` for some local-constant system
   whose base reciprocity component is `e`.

The conclusions are:

- `FullCharacterizationExtendsStatement F`: `ExtendsSupercuspidal F c0 τ`. For
  every irreducible Weil class `σ`, the zero-monodromy class of `σ` exists
  and `τ` sends it to the supercuspidal class `c0 σ`.
- `FullCharacterizationStatement F`: `IsAssemblyOf F c0 τ`, and every full map
  `c` with `IsAssemblyOf F c0 c` equals `τ` (`AssemblyRelation`).

## Sources and provenance

- Henniart 2002, §1.6, printed p.591 (PDF p.5), Corollary: let `(τ_n)` be maps
  `G(n) → A(n)` such that (i) `τ_1` is given by local class field theory, and
  (ii) for all `n, n' ≥ 1`, `σ ∈ G(n)`, `σ' ∈ G(n')`,
  `L(s, τ_n(σ) × τ_n'(σ')) = L(s, σ ⊗ σ')` and
  `ε(s, τ_n(σ) × τ_n'(σ'), ψ) = ε(s, σ ⊗ σ', ψ)`. Then for `σ ∈ G_0(n)`,
  `τ_n(σ) ∈ A_0(n)` and `τ_n(σ) = π^0_n(σ)`. The proof is by induction on
  `n` (§3). `FullCharacterizationExtendsStatement` is this corollary.
- Henniart 2002, §1.8, printed p.592 (PDF p.6), Corollary: under (i)
  `τ_1 = π^0_1` and the same (ii), `τ_n = π_n` for every `n ≥ 1`. The
  uniqueness of the correspondence extended to `G(n)` follows "aussitôt de
  1.4 et du théorème ci-dessus" (Theorem 1.8). `FullCharacterizationStatement`
  is this corollary.
- Henniart 2002, §1.1, printed p.588 (PDF p.2): `π^0_1` is given by local
  class field theory with the geometric normalization, and `ψ` is one fixed
  nontrivial additive character. §1.3, printed p.589 (PDF p.3): `π^0` is the
  supercuspidal family. §2.9, printed p.596 (PDF p.10): `π` is the assembly of
  `π^0` through the Langlands and Zelevinsky classifications.

Source file: `henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Interpretation

- **One additive character.** Hypothesis 4 holds at one arbitrary `ψ`, as in
  Henniart, who fixes `ψ`. This gives the stronger statements. Hypothesis 4
  also contains the existence of a measure self-dual for `ψ`, a true fact that
  the conditions assert so that their `∀ ν` clauses are not vacuous.
- **Rank one.** Henniart's (i) says that `τ_1` is local class field theory,
  normalized as in §1.1. Here it is `RankOneCompatibility F e τ` for a
  geometrically normalized `e`. The same `e` is the base reciprocity
  component of the local-constant system used for the epsilon factors.
- **The supercuspidal family.** Henniart's `π^0` is the family of Theorem 1.3.
  Here `c0` is any map with `IsSupercuspidalCorrespondence F c0`, which
  contains the conditions of Theorem 1.3 and those of Henniart 2000,
  §§1.2–1.3. By the uniqueness of Henniart 2002, §1.4, the two descriptions
  give the same family; the statements hold for every such `c0` and do not
  use that uniqueness.
- **`τ_n(σ) ∈ A_0(n)`.** `ExtendsSupercuspidal` says that `τ` takes the value
  `c0 σ`, a supercuspidal class. This contains Henniart's conclusion that the
  image lies in `A_0(n)`.
- **`π_n` is the assembly.** Henniart's `π_n` is the map built from `π^0` in
  §2.9; here it is the relation `IsAssemblyOf F c0`. As in
  `AssemblyLCharacterizationStatement`, "`τ_n = π_n`" becomes: `τ` is an
  assembly of `c0`, and every assembly of `c0` equals `τ`.
- **No other conditions.** Henniart's hypotheses contain no bijectivity,
  contragredient, determinant or twist condition, and neither do these
  statements.

## Scope

- Henniart's Theorem 1.8, with L-factors against indecomposable parameters of
  smaller rank only, is `AssemblyLCharacterizationStatement` of
  `AssemblyLFactorStatement`. The one-sided results are not statements of this
  task: the Theorem of §1.6 (characterizing `A_0(n)` and `G_0(n)`), the
  Theorem of §1.7 (pole orders) and the gamma-factor results of §1.9.
- The module imports, and does not copy: this task's `FullFactorCompatibility`
  (`FullFactorCompatibilityAt`), `AssemblyLFactorStatement` (and through it
  `AssemblyRelation`, `SupercuspidalSpecification`), `OperationCompatibility`
  (`RankOneCompatibility`, `IsGeometricReciprocity`) and `Domains`
  (`ExtendsSupercuspidal`).

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Both definitions return `Prop`.
