# The tied discrete-series scalar commutant: separated and coincident exponents

Lean module: `Langlands.Representation.Archimedean.RealTiedDiscreteScalarCommutantCases`,
namespace `Langlands.Archimedean`. Author: Worker 380, for Task 6749
(`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`). The split was agreed with Worker 379, who owns
Task 7626 (`4fda7898-2fbf-4ad2-a6b5-48fb114ca3e0`). That task's target
`RealTemperedScalarCommutantStatement` reduces to `RealTiedDiscreteScalarCommutantStatement`
(Library module `RealTiedScalarCommutantCases`) and a statement for lists without a
discrete-series block.

## Purpose and provenance

`RealTiedDiscreteScalarCommutantStatement` asks for a scalar simultaneous commutant on the real
standard module of every list of real blocks that has total rank `n`, equal real exponents and
at least one discrete-series block. This module splits it into two open statements:

* `RealTiedDiscreteSeparatedScalarCommutantStatement`, for lists in which every block with the
  same complex exponent as a discrete-series block is an induction block of the same absolute
  weight (`IsRealDiscreteExponentSeparated`);
* `RealTiedDiscreteCoincidentScalarCommutantStatement`, for the remaining lists.

The theorem `realTiedDiscreteScalarCommutant_of_cases` shows that the two statements together
imply `RealTiedDiscreteScalarCommutantStatement`. The split is internal to this formalization
and has no literature source. It follows the planned proof (see "Status"): the first statement
is the range of a lowest-`O(n)`-type argument, and the second contains the configurations where
that argument is known to fail. Neither statement is proved here.

## Notation

These are Library notions, unchanged.

* `RealBlock`: a block of a real presentation. Either `character c`, the character
  `sgn^ε |·|^t` of `GL_1(ℝ)` with `c.exponent = t`, or `induced d`, the block of `GL_2(ℝ)`
  induced from the character `(z/|z|)^m |z|^(2t)` of `ℂ^×`, with `d.weight = m` and
  `d.exponent = t` (module `ArchimedeanPresentation`, data from `ArchimedeanAttachment`).
* `realRank ds`: the total rank. A character block has rank 1, an induction block rank 2.
* `realBlockExponent x`: the real part of the exponent `t` of `x`
  (module `RealGenericParameterReduction`).
* `IsRealDiscreteSeriesBlock x`: `x` is `induced d` with `d.weight ≠ 0`
  (module `RealTiedScalarCommutantCases`). In `realStandardModule` such a block is
  `D_ℓ ⊗ |det|^t`, `ℓ = |m|`, with lowest `SO(2)`-weight `ℓ + 1` (`StandardModule.md`, item 2).
* `RealTemperedCommutantReduction.HasScalarCommutant n ds`: every complex linear endomorphism of
  the `O(n)`-finite functions of `realStandardModule n ds` that commutes with
  `realStandardRep n ds` and with every `realStandardLie n ds Z` is a complex scalar
  (module `RealTemperedCommutantReduction`).

## Definitions

* `realBlockComplexExponent x : ℂ`: the complex exponent `t` of the block `x`, that is
  `c.exponent` for `character c` and `d.exponent` for `induced d`. Its real part is
  `realBlockExponent x`.
* `realBlockAbsWeight x : Option ℕ`: `none` for `character c`, and `some |m|` for `induced d`
  with `m = d.weight` (Lean: `some d.weight.natAbs`).
* `IsRealDiscreteExponentSeparated ds`: for every `x ∈ ds` with `IsRealDiscreteSeriesBlock x`
  and every `y ∈ ds` with `realBlockComplexExponent y = realBlockComplexExponent x`,
  `realBlockAbsWeight y = realBlockAbsWeight x`. So every block with the same complex exponent
  as a discrete-series block `induced d` is an induction block `induced d'` with
  `|d'.weight| = |d.weight|`, hence itself a discrete-series block. Blocks with weights `m`
  and `-m` may share an exponent. The predicate says nothing about blocks whose exponent is not
  the exponent of a discrete-series block: there, any characters and weight-zero induction
  blocks may occur, with repetitions and with both signs `ε`.
* `RealTiedDiscreteSeparatedScalarCommutantStatement : Prop`: for every `n : ℕ` and every
  `ds : List RealBlock` with

  1. `realRank ds = n`,
  2. `realBlockExponent x = realBlockExponent y` for all `x, y ∈ ds`,
  3. some `x ∈ ds` with `IsRealDiscreteSeriesBlock x`, and
  4. `IsRealDiscreteExponentSeparated ds`,

  `HasScalarCommutant n ds` holds.
* `RealTiedDiscreteCoincidentScalarCommutantStatement : Prop`: the same with hypothesis 4
  replaced by `¬ IsRealDiscreteExponentSeparated ds`.

Hypotheses 1 to 3 are those of `RealTiedDiscreteScalarCommutantStatement`. The two statements
keep its full scope and differ only in hypothesis 4. For every list exactly one version of
hypothesis 4 holds.

## Theorem

`realTiedDiscreteScalarCommutant_of_cases
(ha : RealTiedDiscreteSeparatedScalarCommutantStatement)
(hb : RealTiedDiscreteCoincidentScalarCommutantStatement) :
RealTiedDiscreteScalarCommutantStatement`.

Proof. Let `n`, `ds` satisfy the hypotheses of the target. If `IsRealDiscreteExponentSeparated ds`
holds, apply `ha`; otherwise apply `hb`. This case split on
`IsRealDiscreteExponentSeparated ds` is classical.

## Status and the known obstruction

Both statements are open. Nothing in this section is formalized. It records the planning
analysis behind the split (Worker 380, with Worker 379), so that tasks for the two statements
can cite it.

**Planned route for the separated case.** Write an induction block of weight `m ≠ 0` and exponent
`t` as `D ⊗ |det|^t`. It is a quotient of the principal series `Ind(x, y)` and a subrepresentation
of `Ind(y, x)`, where `x = |·|^{t - |m|/2}` and `y = sgn^{|m|+1} |·|^{t + |m|/2}`. The route
has two steps.

1. Cyclicity. Choose a principal series `ps*` with a surjection `Φ` onto the standard module,
   built from the block quotient maps and swaps of adjacent unlinked characters. Take a vector
   `Φ(v · T'')`. Here `v` is a product of minors of bottom row sets, and `T''` is the
   `O(n)`-fixed vector of a spherical principal series. That spherical vector is assumed cyclic
   (the statement `RealSphericalCyclicStatement` of Task 7626).
2. Scalar step. The vector generates a single `O(n)`-type of multiplicity one, the lowest
   `O(n)`-type. Every simultaneous endomorphism then acts on it by a scalar, and cyclicity
   finishes.

Step 2 needs the rows ordered so that all the `x`-characters lie above all the `y`-characters.
For two discrete-series blocks, the block order `[x₁, y₁, x₂, y₂]` gives a vector whose
`O(4)`-span contains several `O(4)`-types (weights `(k_b + j, k_s - j)`, `j = 0, …, k_s`, where
`k_b ≥ k_s` are the lowest weights). That order does not suffice.

Two characters whose exponents have equal real parts are never linked: the difference of the
exponents is purely imaginary, so it is a nonzero integer never. By hypothesis 2 all blocks have
the same real exponent. Linked pairs can therefore only involve the shifted characters `x` and
`y` of discrete-series blocks, and a character attached to a block of complex exponent `t'`
is linked with `x` or `y` of a block of complex exponent `t` only if `t' = t`.

In the separated case every discrete-series block shares its complex exponent only with
discrete-series blocks of the same absolute weight. Characters belonging to different complex
exponents are unlinked. Within one exponent class of discrete-series blocks, all blocks give the
same pair `x`, `y`, and the route uses the interleaved order and only unlinked swaps. For two
blocks `D`, `D'` of the same absolute weight the path is
`[x, x, y, y] → [x, D, y] → [D, x, y] → [D, D']`.

**Where the route fails ("bad pairs").** Take two induction blocks with the same
complex exponent `t` and weights `m_b`, `m_s` with `|m_b| > |m_s| ≥ 1` and
`|m_b| ≡ |m_s| (mod 4)`. Recall that `Ind(sgn^a|·|^{s₁}, sgn^b|·|^{s₂})` of `GL_2(ℝ)` is
reducible (the pair is linked) exactly when `s₁ - s₂` is a nonzero integer `≡ a - b + 1 (mod 2)`.
The characters `x_b = |·|^{t - |m_b|/2}` and `y_s = sgn^{|m_s|+1} |·|^{t + |m_s|/2}` have
exponent difference `-(|m_b| + |m_s|)/2`, a nonzero integer of the right parity, so they are
linked. The interleaved order puts `x_b` before `y_s`, that is, in increasing order of exponents.
The analysis found two failures. The spherical principal series that the route needs contains
the same linked pair, shifted by the minors and still in increasing order. It is therefore not
reachable from the closed Langlands chamber by unlinked swaps, and the cyclicity input does not
apply. Moreover, every path that `Φ` could take from the interleaved order to the block order
reverses a linked pair of characters (for example `x_b` past `y_s`, directly or inside the block
of `y_s`), and the analysis found no such path made of isomorphisms. Other row orders keep
cyclicity but lose the single lowest `O(n)`-type of step 2. Examples on `GL_4(ℝ)` at `t = 0` are
the weight pairs `(5, 1)` and `(6, 2)`.

All such configurations fail `IsRealDiscreteExponentSeparated`, so they lie in
`RealTiedDiscreteCoincidentScalarCommutantStatement`. The predicate is conservative: the second
statement also contains configurations for which no failure is known. The following list is
planning analysis only. It concerns two blocks with the same complex exponent `t`, at least one
of them a discrete-series block `induced d` with `|d.weight| = ℓ ≥ 1`, `x = |·|^{t - ℓ/2}` and
`y = sgn^{ℓ+1} |·|^{t + ℓ/2}`. A list can combine several of these sub-cases at one exponent or
at several exponents.

Expected to be easy, because there is no linked pair at all:

* two discrete-series blocks of weights `ℓ` and `ℓ'` with `ℓ ≢ ℓ' (mod 2)`;
* a discrete-series block of odd weight `ℓ` and a character block `sgn^ε |·|^t` (either `ε`),
  or an induction block of weight `0`, whose two characters are of this form.

Linked pairs exist, but the analysis found an order of the characters that avoids the
failures above (not checked in detail):

* two discrete-series blocks with `ℓ > ℓ'` and `ℓ - ℓ' ≡ 2 (mod 4)`. Here `x_ℓ`, `x_ℓ'` are
  linked and `y_ℓ`, `y_ℓ'` are linked, but `x_ℓ` and `y_ℓ'` are not. The order
  `[x_ℓ', x_ℓ, y_ℓ', y_ℓ]` reaches the blocks by swapping `x_ℓ` past `y_ℓ'`, and its spherical
  shift is reachable from the closed Langlands chamber by unlinked swaps;
* a discrete-series block of weight `ℓ ≡ 2 (mod 4)` and the character `sgn |·|^t`, which is
  linked with `y` but not with `x`;
* a discrete-series block of weight `ℓ ≡ 0 (mod 4)` and the character `|·|^t`, which is linked
  with `y` but not with `x`.

In these two character cases the order `[x, c, y]` reaches `[c, D]` by swapping `x` past the
character `c`, and its spherical shift is reachable from the closed Langlands chamber by
unlinked swaps.

Known or expected to be hard:

* the bad pairs above: `ℓ > ℓ' ≥ 1` and `ℓ ≡ ℓ' (mod 4)`;
* a discrete-series block of weight `ℓ ≡ 0 (mod 4)` and the character `sgn |·|^t` (also from an
  induction block of weight `0`). The character is linked with `x`, and after the shift by
  the minors it is still linked with `x` and in increasing order when it sits between the `x`-
  and `y`-rows, as the lowest `O(n)`-type requires;
* a discrete-series block of weight `ℓ ≡ 2 (mod 4)` and the character `|·|^t`, which is linked
  with `x`. In the order `[x, c, y]` the spherical shift keeps this linked pair in increasing
  order. The order `[c, x, y]` avoids that, but whether the scalar step survives this placement
  has not been checked.

**Options for the coincident case.** In a bad pair the blocks are not equal, so the Weyl group
stabilizer of the inducing character does not contribute a symmetry there. A Bruhat-type
dimension bound, `dim Hom(Ind(ps*), Ind(ps)) ≤ #{w : w·ps* = ps}`, would then bound the
commutant directly. A translation functor inside a Weyl chamber would also work: `D_6 ⊗ D_2` at
`t = 0` is a regular integral translate of `D_6 ⊗ D_4`, which is not a bad pair. Worker 379
proposed a third option, a connection argument. Suppose every `O(n)`-type in the span of the
generating vector has multiplicity one. Then an endomorphism acts on each type by a scalar.
Adjacent types are joined by a nonzero `𝔭`-matrix coefficient, which forces the scalars to be
equal. This needs explicit matrix coefficients. As of this module the Library has none of these
tools: no Bruhat filtration bound, no translation functors, and no `O(n)` branching rules.
