# Assembly of a full correspondence from a supercuspidal one

Author: Worker 7. This module defines how a supercuspidal map `c0` (from
irreducible Weil classes to supercuspidal classes, `Domains`) determines a full
map on Frobenius-semisimple Weil–Deligne parameters: decompose the parameter
into blocks `σ_i ⊗ Sp(m_i)`, send each block to the special representation of
the segment `[c0 σ_i, ν^(m_i - 1) c0 σ_i]`, and take the Langlands quotient. It
is the construction of Henniart 2002, §§2.2–2.9. The construction is a
relation between classes. The statements that it is well defined, bijective,
extends `c0` and inherits the operation compatibilities are propositions only;
nothing is proved and no correspondence is an input.

## Definitions

`F : PadicField p` carries its canonical topological data `T`, and `ν` is the
normalized absolute value on both sides: `localNormCharacter F` on the Weil
group (`q^(-1)` at geometric Frobenius) and `|det|` on `GL_n(F)`.

- `cuspidalDatumOf F c0 σ`, for an irreducible Weil class `σ` of rank `d + 1`,
  is the published `CuspidalDatum` with rank `d + 1` and class `c0 σ`.
- `segmentOf F c0 σ m` is the published `Segment` with beginning `c0 σ` and
  `m + 1` elements: Zelevinsky's `[c0 σ, ν^m c0 σ]`.
- `multisegmentOf F c0 σ m`, for families `σ_i`, `m_i` indexed by `Fin r`, is
  the multiset of the segments `segmentOf F c0 (σ i) (m i)`.
- `IsBlockSum F σ m D`: there are representatives `B_i` of the classes `σ_i`
  and a representative `A` of `D` with `A` equivalent to the direct sum of the
  published blocks `block ν (B i) (m i + 1)`. A block is the tensor product of
  `(B_i, 0)` with the uncentered special pair `Sp(m_i + 1)`: weights
  `1, ν, …, ν^(m_i)` and the raising monodromy (Tate 1979, §4.1.4).
- `IsMultisegmentHeadClass F c0 σ m π`: some representative of `π` is
  equivalent to a representation `J` with the published
  `Multisegment.IsLanglandsHead (multisegmentOf F c0 σ m) J`. That relation
  says: for some ordering of the multisegment in which no earlier segment
  precedes a later one, and some representations `π_i` that are irreducible
  heads of the segment inductions `i(ρ_i, νρ_i, …)`, `J` is the irreducible
  head of `i(π_1, …, π_r)`. The equivalence crosses carrier universes: `J`
  lives in `max uF uA`, `π` in `uA`.
- `IsAssembledFrom F c0 D π`: for some `r`, ranks `d_i + 1`, lengths
  `m_i + 1` and irreducible Weil classes `σ_i`, `IsBlockSum F σ m D` and
  `IsMultisegmentHeadClass F c0 σ m π`. The decomposition, its order and the
  Langlands ordering are existential data; none is selected.
- `IsAssemblyOf F c0 c`: for every rank `n` and parameter class `D`,
  `IsAssembledFrom F c0 D (c n D)`.

## Statements

- `AssemblyWellDefinedStatement F`: for every supercuspidal map `c0`, rank `n`
  and parameter class `D`, exactly one class `π` satisfies
  `IsAssembledFrom F c0 D π`. Existence needs a block decomposition of `D`
  and the existence of Langlands heads. Uniqueness contains the independence
  of the result from the block decomposition, from the order of the blocks,
  from the choice among admissible orderings (including the order among equal
  exponents) and from the representatives.
- `AssemblyBijectiveStatement F`: if `c0` is bijective in every rank, any
  assembly `c` of `c0` is bijective in every rank (exhaustion and
  injectivity).
- `AssemblyExtendsStatement F`: any assembly `c` of `c0` satisfies the
  published `ExtendsSupercuspidal F c0 c`: on the zero-monodromy class of an
  irreducible Weil class `σ` (one block, `m = 0`), `c` takes the value `c0 σ`.
- `AssemblyOperationStatement F`: if `e` has the geometric normalization and
  `c0` satisfies the supercuspidal rank-one, determinant, twist and dual
  conditions for `e` (`OperationCompatibility`), then any assembly `c` of `c0`
  satisfies the full rank-one, determinant, twist and dual conditions. The
  geometric normalization is needed because `ν` enters both sides: the dual
  of `σ ⊗ Sp(m)` is `ν^(1-m) σ^∨ ⊗ Sp(m)`, and the central character of a
  special representation contains powers of `|det|`.

The inherited pair-factor compatibility, the conditional assembly theorem and
the final unconditional theorem depend on the full-family factor conditions
and on the published classification statements; they are separate modules.

## Sources and provenance

- Henniart 2002, §2.2, printed p.593 (PDF p.7): a representation of `W'_F` is
  a direct sum of indecomposables, and `N[G_2] - {0} → G` is a bijection.
  §2.3, printed p.594 (PDF p.8): an indecomposable is `ρ ⊗ St_n` with `ρ`
  irreducible, where `St_n` restricted to `W_F` is `1 ⊕ ν ⊕ ⋯ ⊕ ν^(n-1)`;
  `(ρ, n) ↦ ρ ⊗ St_n` is a bijection `G_0 × N^* → G_2`.
- Henniart 2002, §2.5, printed pp.594–595 (PDF pp.8–9): `i(π_1, …, π_r)` is
  normalized induction from the upper block parabolic. §2.6, printed p.595:
  `St_n(ρ)` is the unique irreducible quotient of `i(ρ, νρ, …, ν^(n-1)ρ)`
  (Zelevinsky 1980, §9.3). §2.7, printed p.595: `π_2(ρ ⊗ St_n) = St_n(π_0(ρ))`.
- Henniart 2002, §2.8, printed p.596 (PDF p.10): for essentially
  square-integrable `π_1, …, π_r` with `α(π_1) ≥ ⋯ ≥ α(π_r)`, `i(π_1, …, π_r)`
  has a unique irreducible quotient `J`, whose class does not depend on the
  order satisfying this condition; this gives a bijection `N[A_2] - {0} → A`.
  §2.9, printed p.596: the full bijection `π` is `π_2` on blocks, extended
  through these two identifications.
- Tate 1979, §4.1.4, printed p.20 (PDF p.29): the uncentered special pair
  `Sp(n)` with weights `ν^j` and raising monodromy. The published
  `SpecialBlocks` records the construction.
- The segment-head relation (Zelevinsky 1980, §9.1) and the multisegment
  Langlands-head relation (Kudla 1994, Theorem 1.2.5) are recorded by Worker
  23's published `Classification/Segments` and `Classification/LanglandsData`.

**Ordering convention.** Henniart orders the special blocks by decreasing
exponents. The published multisegment relation orders segments so that no
earlier segment precedes a later one. Every ordering by decreasing exponents
is of this kind: if `Δ_1 = [ρ, ν^a ρ]` precedes `Δ_2 = [ν^k ρ, ν^(k+b) ρ]`
(`k ≥ 1`, `k + b > a`), the exponents of their special representations
satisfy `α_2 - α_1 = k + (b - a)/2 > k/2 > 0`. So Henniart's `J` satisfies
the published relation whenever it exists. Conversely, that all admissible
orderings give the same head is part of the classification theorems, stated
by task f72fff19; it is not proved in the Library.

Source files:

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

## Scope

- The parameter side uses the published actual local Weil group, blocks and
  direct sums; nonzero monodromy occurs whenever some `m_i ≥ 1`.
- The representation side uses arbitrary-carrier irreducible admissible
  classes; nongeneric Langlands quotients are included.
- The module imports, and does not copy: `WeilDeligne.SpecialBlocks`
  (`block`), `WeilDeligne.DirectSum` (`directSum`),
  `Classification.Segments` (`CuspidalDatum`, `Segment`, `Multisegment`) and
  `Classification.LanglandsData` (`Multisegment.IsLanglandsHead`), and this
  task's `Domains`, `AutomorphicRelations` and `OperationCompatibility`.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every relation and statement returns
`Prop`; `cuspidalDatumOf`, `segmentOf` and `multisegmentOf` are data
constructors.
