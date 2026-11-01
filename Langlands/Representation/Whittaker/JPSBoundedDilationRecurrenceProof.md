# Uniform-region recurrence for powers of a bounded coordinate dilation (proof)

Authors: Worker 941 (proof draft), Worker 454 (current-Library verification,
documentation and submission). This module proves the published proposition
`Langlands.Whittaker.JPSBoundedDilationRecurrenceStatement.{uF}` from module
`Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement`.

## Closing theorem

`Langlands.Whittaker.jpsBoundedDilationRecurrence :
JPSBoundedDilationRecurrenceStatement.{uF}`, in module
`Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof`. It
proves the whole closed proposition with all its quantifiers and the
unrestricted field universe `uF`. Its only hypotheses are those of the
statement: `HasFiniteCoordinateOperatorSpan W T i` and a unit `c` with
`T.normalizedAbs (c : F.Carrier) ≤ 1`. The rank-zero case needs no separate
argument, since `i : Fin 0` cannot be given. It intros the data and applies
`JPSBoundedDilationRecurrenceProof.recurrence_of_finiteSpan`.

## Dependencies

- `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement`
  (the target) and, through it, `Langlands.Representation.Whittaker.JPSFunctionSpace`:
  `coordinateRepresentation_apply`, `coordinateEmbedding_same`,
  `germMap_eq_zero_iff`, `sigma_apply_mk`, `coordinateVanishing`,
  `VanishesNearCoordinateZero`, `HasFiniteCoordinateOperatorSpan`.
- `T.normalizedAbs_mul`, `T.normalizedAbs_one`, `T.normalizedAbs_nonneg` for
  the normalized absolute value.
- Mathlib: `Mathlib.LinearAlgebra.FiniteDimensional.Basic` and
  `Mathlib.RingTheory.Noetherian.Basic` (`monotone_stabilizes_iff_noetherian`,
  `IsNoetherian.iff_fg`, `Submodule.mem_span_range_iff_exists_fun`,
  `Submodule.fg_iff_finiteDimensional`).

No other substantial result is used.

## Conventions

`|x|` is `T.normalizedAbs x`. `ρ_i` is `coordinateRepresentation W i`, with
`(ρ_i(b) f)(a) = f (a · e_i(b))`. `σ_i` is `sigma W T i` on the actual quotient
`CoordinateGerm W T i = W / W_i`, where `W_i = coordinateVanishing W T i`.
The absolute value is the published residue-cardinality normalization:
`T.normalizedAbs 0 = 0` and `T.normalizedAbs x = q ^ (-T.ord x)` for nonzero
`x`, with `q = T.residueCardinality`. The proof uses its multiplicativity,
nonnegativity and value at one. No topology is installed or used.

## Helper declarations (namespace `Langlands.Whittaker.JPSBoundedDilationRecurrenceProof`)

- `normalizedAbs_pow_le_one`: `|c| ≤ 1` gives `|c ^ m| ≤ 1`, by induction with
  `normalizedAbs_mul`.
- `exists_common_threshold`: finitely many threshold properties that are
  closed under shrinking have one common positive threshold (the minimum, by
  induction on the finite set).
- `smallVanishing W T i δ`: the submodule of `f` with `f a = 0` whenever
  `|a_i| < δ`. It is antitone in `δ` (`smallVanishing_anti`). By
  `germMap_eq_zero_iff`, its elements for `δ > 0` have zero germ
  (`germMap_eq_zero_of_mem_smallVanishing`), and every zero-germ function lies
  in some `smallVanishing W T i δ` with `δ > 0` (`exists_mem_smallVanishing`).
- `coordinateRepresentation_mem_smallVanishing`: for `|c| ≤ 1`, `ρ_i(c)` maps
  `smallVanishing W T i δ` into itself, because `|a_i c| ≤ |a_i| < δ`.
- `exists_threshold_of_finiteDimensional`: a finite-dimensional submodule of
  zero-germ functions is contained in one `smallVanishing W T i δ`, `δ > 0`
  (take a finite spanning set and `exists_common_threshold`).
- `pow_mem_sup`: if
  `ρ_i(c ^ D) g - ∑_{j<D} e_j ρ_i(c ^ j) g ∈ smallVanishing W T i δ` and
  `|c| ≤ 1`, then every `ρ_i(c ^ m) g` lies in
  `span{ρ_i(c ^ j) g | j < D} ⊔ smallVanishing W T i δ`. Strong induction on
  `m`: for `m < D` it is a spanning vector; for `m = s + D`,
  `ρ_i(c ^ (s+D)) g = ρ_i(c ^ s)(relation) + ∑_j e_j ρ_i(c ^ (s+j)) g`, the
  first term is in `smallVanishing` by the previous item and `|c ^ s| ≤ 1`,
  and each `s + j < s + D` is covered by induction.
- `exists_pow_mem_span`: there is `D` with every `σ_i(c ^ m)` in the span of
  `σ_i(c ^ j)`, `j < D`. Inside the finite-dimensional, hence Noetherian, span
  `S` of the range of `σ_i`, the increasing chain
  `N d = span{σ_i(c ^ j) | j < d}` stabilizes at some `D`
  (`monotone_stabilizes_iff_noetherian`). For `m ≥ D`, `σ_i(c ^ m) ∈ N (m+1) = N D`.
  The coefficients are transported from `S` to `Module.End` by `Subtype.val`.

## Main argument (`recurrence_of_finiteSpan`)

1. *`D` and `d` before `f`.* `exists_pow_mem_span` gives `D`; `choose` on
   `Submodule.mem_span_range_iff_exists_fun` gives `d m : Fin D → ℂ` with
   `∑_j d m j • σ_i(c ^ j) = σ_i(c ^ m)` for every `m`. Neither depends on `f`.
2. *Germ relations.* For every `m`, by `sigma_apply_mk`, the function
   `ρ_i(c ^ m) f - ∑_j d m j • ρ_i(c ^ j) f` has zero germ.
3. *First threshold.* The relation at `m = D` lies in some
   `smallVanishing W T i δ₁`, `δ₁ > 0`.
4. *Second threshold.* `L = span{ρ_i(c ^ j) f | j < D}` is finite-dimensional;
   so is `P = L ⊓ W_i`, which by `exists_threshold_of_finiteDimensional` lies
   in some `smallVanishing W T i δ₂`, `δ₂ > 0`.
5. *Threshold `δ = min δ₁ δ₂`*, chosen before `m` and `a`. Fix `m` and `a` with
   `|a_i| < δ`. By `pow_mem_sup` (with `e = d D`) and the span membership of
   the sum, `H = ρ_i(c ^ m) f - ∑_j d m j • ρ_i(c ^ j) f` is `z + e` with
   `z ∈ L` and `e ∈ smallVanishing W T i δ₁`. Both `H` (step 2) and `e` have
   zero germ, so `z ∈ W_i`, hence `z ∈ P` and `z a = 0`; also `e a = 0`. So
   `H a = 0`, which unfolds by `Submodule.coe_*` and `Finset.sum_apply` to the
   pointwise identity.

## Uniformity

`D` and `d` are fixed in step 1 before `f`. The threshold `δ` depends on `f`
only through `δ₁` (one relation) and `δ₂` (one finite-dimensional space),
and is fixed before `m` and the whole tuple `a`. `|c| ≤ 1` is used in
`pow_mem_sup` through `normalizedAbs_pow_le_one` and
`coordinateRepresentation_mem_smallVanishing`.

## Source

This is a derived intermediate result, not a displayed theorem of the source.
H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212, is registered as
`jps-1979-gl3-i`, PDF SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
The route follows its finite-algebra remarks on printed p.181
(every element of `𝒜` satisfies a polynomial equation), and the uniform-region
step in the proof of Lemma (2.2.1), printed p.182 (registered source
`jps-1979-gl3-i`, PDF pp.14–15). The implementation uses Noetherian chain
stabilization in place of a polynomial equation.

## Checks

The submitted proof is checked in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with the closing constant inspected
unapplied and assigned directly to the target in a private check. Formal
acceptance additionally requires the exact-target and Lake-build validation
and independent semantic review.
