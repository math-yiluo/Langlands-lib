# Pair L- and epsilon-factor compatibility of full families

Author: Worker 7. This module states the pair epsilon-factor condition for the
full family `FullMap` of `Domains`. It then combines it with the L-factor
condition of `FullLFactorCompatibility` into the full pair-factor condition.
The full family sends Frobenius-semisimple Weil–Deligne parameter classes,
nonzero monodromy allowed, to classes of irreducible admissible
representations of `GL_n(F)`, nongeneric ones included. The epsilon condition
is `ε(s, π(D) × π(D'), ψ) = ε(s, D ⊗ D', ψ)` for all ranks `n, n' ≥ 1`. All
conditions are propositions about a given map. No map, additive character,
measure or local-constant system is constructed or chosen, and no part of the
correspondence is asserted.

## Representation side

`F : PadicField p` carries its canonical topological data and `q` is its
residue cardinality. Automorphic classes are the published
`AutomorphicClass F n`: isomorphism classes of the irreducible admissible
smooth representations of `GL_n(F)`, with carriers in universe `uA`.

`IsAutomorphicPairEpsilonFactor F ψ ν π π' e`, for classes `π` of rank `r + 1`
and `π'` of rank `t + 1` and `e = (c, m) : ℂˣ × ℤ`, says
`ε(s, π × π', ψ) = c q^(-ms)`. Precisely, there are representatives `A` of `π`
and `A'` of `π'`, and representations `J`, `J'` with carriers in universe
`max uF uA`, such that:

- `J` is equivalent to `A` and `J'` to `A'`; and
- Worker 31's `RankinSelberg.IsLanglandsPairEpsilonFactor.{uF, uA, uA}
  F ψ ν J J' e` holds (module `RankinSelberg/LanglandsFactors`, task
  6f0365a3).

That relation is the epsilon factor of Henniart 2002, §2.8, defined through
the Langlands classification. Both `J` and `J'` are Langlands quotients of
square-integrable Langlands data: finite families of irreducible essentially
square-integrable blocks, ordered by nonincreasing unitary exponent. For every
pair of such data, there are block epsilon factors whose coefficients
multiply, and whose exponents add, to `e`. Each block factor satisfies the
published JPSS relation `IsPadicSymmetricEpsilonFactor` at the same `ψ` and
`ν`. So the relation also covers nongeneric `J`, `J'`. The relation takes its
representations in universe `max uF uA` and its blocks in `uA`, while class
representatives live in `uA`. The equivalence therefore crosses carrier
universes, as for the L relation of `FullLFactorCompatibility`.

## Arithmetic side

`IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c m` of `ArithmeticFactors` says
that the Langlands–Deligne epsilon factor of the tensor product of the
Weil–Deligne pair classes `X` and `Y` is `c q^(-ms)`. It is computed with the
supplied local-constant system `ε`, for the reciprocity family `eC`, with
`hε : IsSystem F eC ε`, at a measure self-dual for `ψ`. The tensor product
keeps its monodromy, which enters through the inertia invariants of the
kernel of `N`. Here `X` and `Y` are `parameterForget F D` and
`parameterForget F D'`, the Weil–Deligne classes underlying the
Frobenius-semisimple classes `D` and `D'`.

## Conditions

- `IsPairEpsilonCompatibleAt F eC ε hε ψ D D' π π'`, for parameter classes `D`
  of rank `r + 1` and `D'` of rank `t + 1`, and automorphic classes `π`, `π'`
  of the same ranks, says:
  1. a measure `ν` self-dual for `ψ` exists (`IsSelfDualMeasure` of
     `LocalConventions`); and
  2. for every such `ν`, there is `e : ℂˣ × ℤ` with
     `IsAutomorphicPairEpsilonFactor F ψ ν π π' e` and
     `IsArithmeticPairEpsilonFactor F eC ε hε ψ (parameterForget F D)
     (parameterForget F D') e.1 e.2`.
- `FullPairEpsilonCompatibilityAt F eC ε hε ψ c`, for a full map `c`: for all
  `r t : ℕ` and all parameter classes `D` of rank `r + 1` and `D'` of rank
  `t + 1`, `IsPairEpsilonCompatibleAt F eC ε hε ψ D D' (c D) (c D')`.
- `FullPairEpsilonCompatibility F eC ε hε c`: the same for every nontrivial
  unitary additive character `ψ` of `F`.
- `FullEpsilonCompatibility F e c`, for a rank-one reciprocity candidate `e`:
  some reciprocity family `eC`, assignment `ε` and proof
  `hε : IsSystem F eC ε` exist with `IsBaseReciprocity F e eC` and
  `FullPairEpsilonCompatibility F eC ε hε c`.
- `FullFactorCompatibility F e c`: `FullPairLCompatibility F c` and
  `FullEpsilonCompatibility F e c`. Both L and epsilon are required for every
  nontrivial `ψ`, with the same map `c`.
- `FullFactorCompatibilityAt F e ψ c`, at one nontrivial `ψ`:
  `FullPairLCompatibilityAt F ψ c`, and some system `(eC, ε, hε)` with
  `IsBaseReciprocity F e eC` satisfies
  `FullPairEpsilonCompatibilityAt F eC ε hε ψ c`. This is the hypothesis of
  Henniart's Corollaries 1.6 and 1.8 (`FullCharacterizationStatement`).

Ranks are written `r.succPNat` for classes and `r + 1` for representations;
these agree definitionally, so no rank casts occur.

## Sources and provenance

- Henniart 2002, §1.2, printed pp.588–589 (PDF pp.2–3): the epsilon factors
  are those of Langlands and Deligne for representations of `W'_F`, and those
  of JPSS for pairs `π × π'`. L-factors have the form `P(q^(-s))⁻¹` with
  `P(0) = 1`, and epsilon factors the form `α q^(-ms)` with `α ∈ ℂˣ` and
  `m ∈ ℤ`. §1.5, printed p.590 (PDF p.4), Theorem (iii): the full bijections
  satisfy `L(s, π_n(σ) × π_n'(σ')) = L(s, σ ⊗ σ')` and
  `ε(s, π_n(σ) × π_n'(σ'), ψ) = ε(s, σ ⊗ σ', ψ)` for all `n, n' ≥ 1`,
  `σ ∈ G(n)`, `σ' ∈ G(n')`. This module states the epsilon identity as a
  condition on an arbitrary full map.
- Henniart 2002, §1.6, printed p.591 (PDF p.5), Corollary, and §1.8,
  printed p.592 (PDF p.6), Corollary: hypothesis (ii) is the L and epsilon
  identities for all `n, n' ≥ 1` and all `σ ∈ G(n)`, `σ' ∈ G(n')`, at the
  fixed `ψ`. `FullFactorCompatibilityAt` is this hypothesis.
- Henniart 2002, §2.8, printed p.596 (PDF p.10): `A` is identified with
  `N[A_2] - {0}` through the unique irreducible quotient
  `J(π_1, …, π_r)` of `i(π_1, …, π_r)`, for essentially square-integrable
  `π_i` ordered by nonincreasing exponent, citing Casselman 1977 and JPSS
  1983, Introduction. For `π = Σ π_i` and `π' = Σ π'_j`,
  `ε(s, π × π') = Π_(i,j) ε(s, π_i × π'_j, ψ)`, with the same `ψ` in every
  factor. This is the definition that Worker 31's
  `IsLanglandsPairEpsilonFactor` implements.
- Harris–Taylor 2001, Introduction, printed pp.1–2 (PDF pp.9–10), property 2:
  a local Langlands correspondence matches `L(π_1 × π_2, s)` and
  `ε(π_1 × π_2, s, ψ)` with the factors of the tensor product of the
  parameters, for the fixed nontrivial `ψ`.
- Tate 1979, (3.6.4), printed p.17 (PDF p.26): Langlands' `ε(s, V, ψ)` is
  Deligne's constant at the measure self-dual for `ψ`. JPSS also use the
  self-dual measure (recorded in the published `RankinSelberg/EpsilonFactor`,
  JPSS pp.377–378). Hence the measure in the condition is self-dual.
- Henniart 2000, §1.3, remark, printed p.441 (PDF p.3): for a family with the
  central-character property, the epsilon identity for one `ψ` implies it for
  every `ψ`.

Source files:

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

## Interpretation

- **Every `ψ`.** `FullPairEpsilonCompatibility` and `FullFactorCompatibility`
  quantify over all nontrivial `ψ`, with one map `c`. Henniart and
  Harris–Taylor fix one `ψ`. For families with the central-character
  property, which the full specification requires separately, the two forms
  agree by Henniart 2000, §1.3; that remark is not proved in the Library.
  `FullFactorCompatibilityAt` is the one-`ψ` form used by the
  characterization statements.
- **Both L and ε.** The L identity and the epsilon identity are separate
  conjuncts. A gamma identity does not replace them; it is the derived
  statement of `FullGammaCompatibility`.
- **Totality.** The witness `e` is asserted to exist. So the condition implies,
  and does not assume, that every image class is the Langlands quotient of
  square-integrable data and that all block epsilon factors exist. Worker
  31's module keeps the existence of block factors and the independence of the
  data as explicit inputs of its constructor; it does not prove them.
- **Measures.** A self-dual measure for `ψ` is asserted to exist, so the
  `∀ ν` clause is not vacuous, and the identity is required for every
  self-dual measure. The witness `e` may a priori depend on `ν`. The
  published uniqueness `IsLanglandsPairEpsilonFactor.unique` and the measure
  independence of the arithmetic side make that dependence harmless.
- **Local constants.** As in `SupercuspidalFactorCompatibility`, the system
  is existentially quantified with its base reciprocity component `e`.
  Deligne's theorem gives existence and uniqueness of such a system; the
  Library states these as `NonabelianSystem.Exists` and
  `NonabelianSystem.Unique` without proof.
- **Representatives.** The relation is existential in the representatives
  and in the equivalent representations `J`, `J'`. Henniart 2002, §1.2,
  remark, printed p.589: the factors depend only on the isomorphism classes.
- **Rank order.** Each block factor follows the convention of the published
  `PadicPairFactors`: the block of larger rank is read first, and at equal
  rank the given order is kept. The condition is stated for both orders of
  `(D, D')`.

## Scope

- The module imports, and does not copy: Worker 31's
  `RankinSelberg/LanglandsFactors` (`IsLanglandsPairEpsilonFactor`), this
  task's `FullLFactorCompatibility` (`FullPairLCompatibility`,
  `FullPairLCompatibilityAt`), `ArithmeticFactors`
  (`IsArithmeticPairEpsilonFactor`, `IsBaseReciprocity`), `Domains`,
  `AutomorphicRelations`, `OperationCompatibility` (`ReciprocityCandidate`)
  and `LocalConventions`.
- The two topology instances on `F` and on `GL_n(F)` are local and have
  explicit names (`fullFactorFieldTopology`, `fullFactorGeneralLinearTopology`),
  so the module can be imported together with the other modules of this task.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every condition returns `Prop`.
