# The tied scalar commutant: lists with and without a discrete-series block

Lean module: `Langlands.Representation.Archimedean.RealTiedScalarCommutantCases`, namespace
`Langlands.Archimedean`. Its target is
`RealTemperedScalarCommutantStatement` (Library module `RealTemperedCommutantReduction`).

## Purpose and provenance

The target asks for a scalar simultaneous commutant on the real standard module of every list
of real blocks that has total rank `n` and equal real exponents. This module splits that target
into two statements:

* `RealTiedNondiscreteScalarCommutantStatement`, for lists without a discrete-series block;
* `RealTiedDiscreteScalarCommutantStatement`, for lists with at least one discrete-series
  block.

The theorem `realTemperedScalarCommutant_of_cases` shows that the two statements together imply
the target. The split is internal to this formalization and has no literature source. It follows
the planned proof. The case without discrete-series blocks reduces to cyclicity of the
`O(n)`-fixed vector in spherical principal series. The case with a discrete-series block needs
a separate argument. Neither statement is proved here.

## Notation

These are all Library notions, unchanged.

* `RealBlock`: a block of a real presentation. It is either `character c`, a character
  `sgn^ε |·|^t` of `GL_1(ℝ)`, or `induced d` for complex character data `d`, whose
  `d.weight : ℤ` is the weight `m` and whose `d.exponent` is `t`.
* `realRank ds`: the total rank, where a character block has rank 1 and an induction block
  rank 2.
* `realBlockExponent x`: the real part of the exponent `t` of the block `x`
  (module `RealGenericParameterReduction`).
* `RealTemperedCommutantReduction.HasScalarCommutant n ds`: every complex linear endomorphism of
  the `O(n)`-finite functions of `realStandardModule n ds` that commutes with
  `realStandardRep n ds` and with every `realStandardLie n ds Z` is multiplication by a complex
  scalar (module `RealTemperedCommutantReduction`).

## Definitions

* `IsRealDiscreteSeriesBlock x`: the block `x` is `induced d` with `d.weight ≠ 0`. It is false
  for character blocks and for induction blocks of weight `0`.

  Meaning. In `realStandardModule` an induction block of weight `m` with `|m| = ℓ ≥ 1` gives
  the functions of the principal series whose Fourier coefficients of weight `|k| < ℓ` along the
  block rotations vanish. `StandardModule.md` (item 2, "The discrete series block") identifies
  this block with `D_ℓ ⊗ |det|^t`, a relative discrete series of `GL_2(ℝ)` with lowest
  `SO(2)`-weight `ℓ + 1`, in the notation of Knapp's (2.2b) as recorded there. For weight `0`, the
  Library's `realBlockExpand` replaces the block by the two characters `sgn·|·|^t` and `|·|^t`.
  The predicate only records the condition `d.weight ≠ 0`. The identification with the discrete
  series is not part of the Lean definition.

* `RealTiedNondiscreteScalarCommutantStatement : Prop`: for every `n : ℕ` and every
  `ds : List RealBlock` with

  1. `realRank ds = n`,
  2. `realBlockExponent x = realBlockExponent y` for all `x, y ∈ ds`, and
  3. `¬ IsRealDiscreteSeriesBlock x` for every `x ∈ ds`,

  `HasScalarCommutant n ds` holds.

* `RealTiedDiscreteScalarCommutantStatement : Prop`: for every `n : ℕ` and every
  `ds : List RealBlock` with

  1. `realRank ds = n`,
  2. `realBlockExponent x = realBlockExponent y` for all `x, y ∈ ds`, and
  3. some `x ∈ ds` with `IsRealDiscreteSeriesBlock x`,

  `HasScalarCommutant n ds` holds.

Hypotheses 1 and 2 are those of `RealTemperedScalarCommutantStatement`. The two statements
differ only in hypothesis 3. For every list, exactly one of the two versions of hypothesis 3
holds. The empty list falls under the first statement.

## Theorem

`realTemperedScalarCommutant_of_cases (h₁ : RealTiedNondiscreteScalarCommutantStatement)
(h₂ : RealTiedDiscreteScalarCommutantStatement) : RealTemperedScalarCommutantStatement`.

Proof. Let `n`, `ds` satisfy the hypotheses of the target. If some block of `ds` is a
discrete-series block, apply `h₂`. Otherwise every block of `ds` fails
`IsRealDiscreteSeriesBlock`, so `h₁` applies.

## Status

Both statements are proved, and `realTemperedScalarCommutant` (module
`RealTemperedScalarCommutantProof`) combines them by the theorem above. The first follows from
the spherical cyclicity statement `RealSphericalCyclicStatement` (module `RealSphericalCyclic`,
proved in `RealSphericalCyclicProof`) by `realTiedNondiscreteReduction` (module
`RealTiedScalarAssembly`). The second is split in `RealTiedDiscreteScalarCommutantCases` into
two cases, proved in `RealDiscreteSeparatedProof` and `RealDiscreteCoincidentProof`.
