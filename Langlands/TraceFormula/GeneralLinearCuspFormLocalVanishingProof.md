# Cusp forms at one finite place give vanishing two-block unipotent integrals

`Langlands.TraceFormula.generalLinearCuspFormLocalVanishing.{u}` proves
[`GeneralLinearCuspFormLocalVanishingStatement.{u}`](GeneralLinearCuspFormLocalVanishingStatement.md).
For each pair of adelic translates, it takes the vanishing constant term on the
standard two-block unipotent radical to the integral in rectangular matrix
coordinates with the given additive Haar measure.

## Proof

Substitute `n = a + b` and take `B = Langlands.Shahidi.twoBlocks a b ha hb`.
The consecutive index lemmas `twoBlocks_index_first` and `twoBlocks_index_second`
identify the block indices with `Fin.castAdd b` and `Fin.natAdd a`. The entry formula
for `blockUnipotent` follows from `blockUnipotent_val`. The zero lower-left block
and the two identity diagonal blocks give membership in the radical by
`twoBlocks_mem_parabolic_iff` and `BlockShape.mem_unipotentSubgroup_iff`.

The private `twoBlockUnipotentEquiv` sends a matrix `Z` to `blockUnipotent rfl Z`
in the radical and extracts the upper-right submatrix in the opposite direction.
Extracting that block recovers `Z`. For the other inverse law, the radical
conditions determine the three remaining blocks.
`blockUnipotent_add` gives the group law on matrices viewed through the
`Multiplicative` type tag. `continuous_blockUnipotent` and continuity of
submatrix extraction give continuity in both directions.

Over `R = FiniteCompletion K v`, the type tag carries the same topology and
Borel σ-algebra as the underlying matrix space. Its multiplication is matrix
addition, so the given additive Haar measure `ν` becomes a multiplicative Haar
measure there. `ContinuousMulEquiv.isHaarMeasure_map` makes its pushforward `μ`
a Haar measure on `B.unipotentSubgroup R`. The subgroup has the subspace Borel
σ-algebra induced by `GeneralLinear (a + b) R`, as used by
`Langlands.BaseChange.HasVanishingConstantTerms`.

For the fixed adelic translates `x, y`, apply `HasVanishingConstantTerms` to `B`
and `μ`. Its `IsUnipotentCuspidal` component at the local identity translates
gives the zero integral on the radical. The measurable equivalence underlying
`twoBlockUnipotentEquiv` gives the change of variables by `integral_map_equiv`,
yielding the requested integral against `ν`.

## Source correspondence

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Definition
  16.4.1 and the proof of Lemma 16.4.2, printed p. 430 (PDF p. 438). The definition
  gives the vanishing integrals over local unipotent radicals, which the lemma
  uses at a finite place to obtain cuspidal image. This proof writes that local
  integral in the matrix coordinates for the standard two-block radical of
  `GL_n`. Registered source `getz-hahn-2024-automorphic-representations`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle* (2011), II.6.3, printed p. 120 (PDF p. 128),
  condition `c_{v₁}(f)`. Their finite-place hypothesis combines elliptic support
  with an expression in matrix coefficients of cuspidal representations. It
  motivates the local cuspidality assumption here. The Lean proof starts from
  vanishing constant terms of the local slices and uses a coordinate change
  internal to the Library. Registered source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
