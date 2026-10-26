# Scalar norms of Jacquet exponents of a segment special quotient

Author: Worker 561.

`Langlands.Classification.SegmentSpecialJacquetExponentNormFormula` is a
proposition definition. It states an algebraic formula; this module supplies no
proof of that formula.

For any prime `p`, finite p-adic extension `F : PadicField.{uF} p`, and
`T : F.TopologicalData`, use the topology supplied by `T`. The field and
representation universes `uF` and `uV` are independent. The segment classes,
the supplied supercuspidal representative, and the smooth quotient have
carriers in `Type (max uF uV)`. This saturation also accommodates the actual
induced representation.

The segment is `Δ = [ρ, ν^(m-1)ρ]`, where `r = Δ.rank > 0`, `m = Δ.length > 0`,
and `ν = |det|` uses the residue-normalized absolute value of `T`.
The statement quantifies every representative `A` of `Δ.base` and every
supplied character `ω : Fˣ →* ℂˣ` acting on `A` along the actual scalar-matrix
inclusion. It assumes neither unitarity nor a chosen real part of `ω`.

## Quotient and exponent semantics

The representation `π` is an actual smooth representation of `GL_(mr)(F)`.
The only constituent hypothesis is `T.IsSegmentQuotient Δ π`: for some actual
supercuspidal representative of the base, there is a surjective intertwiner
from the increasing normalized induction
`A × νA × ⋯ × ν^(m-1)A` onto the irreducible `π`.
The relation supplies no uniqueness of quotient kernels. The supplied `A`
may differ from that existential representative; the published representative
transport in `Segments` relates their inductions.

For every standard block shape `B` of `mr`, including the whole-block shape,
the statement quantifies all characters `χ : (Fin B.length → Fˣ) →* ℂˣ`
satisfying `T.IsJacquetExponent B π.representation χ`.
This predicate means that `χ` has open kernel and that the actual normalized
Jacquet module restricted to block scalars has a nonzero vector annihilated
by one common power of each operator `ρ_B(a) - χ(a)`.
Thus the quantifier covers all generalized eigencharacters, without choosing
irreducible Jacquet constituents or assuming an ordinary eigenvector.

The conventions are those of the imported constructions: induction from the
standard upper block parabolic has covariance by the positive half-modulus and
acts by right translation. The normalized upper Jacquet action on classes is
`a · [v] = δ_B(a)^(-1/2)[π(a)v]`. No additional half-modulus factor occurs in
the displayed norm formula.

## Formula

For each exponent, there must be positive integers `k i` such that

```
B.size i = r * k i,       ∑ i, k i = m.
K i = ∑ j : Fin B.length with j < i, k j.
E i = (r : ℝ) * (k i : ℝ) *
      (((2 * (m : ℝ) - (k i : ℝ) - 1) / 2) - (K i : ℝ)).
```

Here `K i` is the total length of the earlier blocks in their given order.
Every subtraction and division in `E i` takes place in `ℝ`; only `K i`
is first computed as a natural-number sum. The assertion is

```
‖χ(a)‖ = ∏ i, (‖ω(a i)‖ ^ k i * |a i| ^ E i)
```

for every block-scalar family `a`. The product includes both factors inside
each parenthesis. The power of `‖ω(a i)‖` is a natural power, and that of
`|a i| = T.normalizedAbs (a i)` is a real power. In particular, existence
of an exponent forces every block size to be divisible by `r`.

This formula sums the scalar contributions of successive descending intervals
of lengths `k i` in `m-1, m-2, …, 0`. The interval for block `i` runs from
`m-1-K i` down to `m-K i-k i`. Its endpoint sum is
`k i * ((2*m-k i-1)/2-K i)`. Each determinant twist of a rank-`r`
supercuspidal contributes an additional factor `r` on scalar matrices.
This arithmetic explains the stated exponent; it is not a proof that these
are all Jacquet exponents.

For the whole-block shape, the sum condition forces `k 0 = m` and `K 0 = 0`.
The formula becomes

```
‖χ(a)‖ = ‖ω(a 0)‖ ^ m * |a 0| ^ (r*m*(m-1)/2).
```

This is the expected scalar norm of the increasing segment induction and its
special quotient, consistent with the separate proposition definition
`SegmentConstituentCentralCharacter`. The present file does not invoke a proof
of that proposition. When `m = 1` the assertion allows only the whole block and
reduces to the supplied scalar norm. For a centered rank-one segment of length
two the two singleton blocks give the usual exponents `1/2, -1/2`.

## Original source and derivation boundary

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
165–210, source ID `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

Section 9.1, printed p.197 / PDF p.34, identifies the special representation
`⟨Δ⟩^t` as the unique irreducible quotient of the increasing product and gives
the descending minimal normalized Jacquet tensor in equation (*).
Section 9.5, printed p.198 / PDF p.35, gives the two-block Jacquet formula
and vanishing when a block size is not divisible by the cuspidal rank.
The half-modulus conversion is explicitly flagged in §9.3 on that same page;
the formal statement retains the actual Library normalizations described above.
Both pages were read and the formulas checked against their images.

The exact general-block norm statement, especially its quantification over all
generalized eigencharacters, is a derived formulation. It requires iteration
of the two-block calculation through normalized Jacquet transitivity, together
with scalar-character computations and transfer to every generalized character.
It is not quoted verbatim from Zelevinsky. The source's notation uses `m` for
the cuspidal rank in §9.5; this file uses `r` for that rank and `m` for the
number of segment terms.

The public source-boundary note
[`gln-classification-sources.md`](../../../notes/henniart/gln-classification-sources.md)
distinguishes the special quotient from the increasing-product submodule and
records corrections to Auel's later classification argument. Those
classification and analytic results are not inputs here. No source-specific
Zelevinsky errata file was present in the current public notes.

## Missing proof obligations and independence

A proof must justify the calculation for every weak segment quotient, including
representative transport and any needed independent algebraic special-quotient
uniqueness; the two-block Jacquet formula and its divisibility vanishing;
normalized transitivity for arbitrary ordered shapes; scalar-character
calculations and their passage to all generalized eigencharacters; and the
finite interval arithmetic in the actual normalization.
Any admissibility or finite-length facts used for character transfer must
themselves be proved or independently available.
The existing constituent-existence, general scalar-compatibility,
admissibility and Casselman tasks remain distinct obligations.

No analytic square-integrability, invariant positive Hermitian form,
temperedness, converse, classification or exhaustion theorem occurs as a
hypothesis or conclusion. The proof successor must remain independent, directly
and transitively, of the forward special-square-integrability proof, its parent
ordered conversion, square-integrable or regular exhaustion, strong-head
analytic classification, tempered block uniqueness, multisegment exhaustion,
ordered-head existence, quotient coverage, and their downstream consequences.
Zelevinsky §9.3's analytic result and §9.17's conjecture cannot supply this
algebraic input. Shared lower-level results require an independence check.
Statement publication, bibliographic formulas and pending tasks do not
constitute a proof.
