# Fitting stabilization of compact compressed actions

This module proves the exact published proposition
`Langlands.Jacquet.CompactCompressionStabilizationStatement.{uG, uV}` from
`Langlands.Representation.Jacquet.CompressionStabilizationStatement`.
The closing theorem is
`Langlands.Jacquet.compactCompression_stabilization`.
The statement and its imported constructions are used unchanged.

The group and representation carrier have independent universes. For every
topological group `G`, complex representation `ρ` on `V`, smoothness witness
`hρ`, compact open subgroup `K` with compactness witness `hK`, and arbitrary
`g : G`, the only dimension assumption is
`FiniteDimensional ℂ (Langlands.fixedVectors ρ K.toSubgroup)`.
There is no dimension or nontriviality assumption on `V`. Zero fixed-vector
modules and zero representation carriers are included.

## Implemented proof

Put `W = Langlands.fixedVectors ρ K.toSubgroup` and
`C = Langlands.Jacquet.compressedAction ρ hρ K hK g`.
This is the existing normalized compact compression acting on the actual
fixed-vector module. Its stable image `S` is the intersection of the ranges of
all powers `C ^ n`; its power-kernel supremum `T` is the supremum of their
kernels, in both cases including exponent zero.

The proof installs the given finite-dimensional structure on `W`. Mathlib
then supplies the Artinian and Noetherian instances used by its Fitting theory.
It combines `LinearMap.eventually_iInf_range_pow_eq` with
`LinearMap.eventually_iSup_ker_pow_eq` using `Filter.Eventually.and` and
extracts a common threshold using `Filter.eventually_atTop.mp`. Thus there is
one `r : ℕ` such that every `s ≥ r` satisfies both
`S = LinearMap.range (C ^ s)` and `T = LinearMap.ker (C ^ s)`.
Combining the two eventual statements in the filter supplies the common
threshold directly.

Next, `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow C` gives `IsCompl T S`.
The definitions of the published `powerKernelSup` and `stableImage` identify
the submodules in this Mathlib result with the requested ones.

For bijectivity, the proof uses the existing `stableImageAction`, which is the
restriction of `C` to the actual carrier of `S`. It first proves that this
linear map has zero kernel. If `v` belongs to its kernel, taking `Subtype.val`
gives `C v = 0` in `W`. Hence the underlying vector belongs to
`LinearMap.ker (C ^ 1)`, and therefore to `T`. It also belongs to `S` by its
subtype property. The disjointness in `IsCompl T S` forces this vector to be
zero, and subtype extensionality gives `v = 0`. Finally,
`LinearMap.injective_iff_surjective` applies to this endomorphism of `S`,
whose finite dimensionality is inherited from `W`, and supplies surjectivity.

## Named consequences

All declarations below are in `Langlands.Jacquet`. For the first three,
the arguments are `ρ hρ K hK g hfin`, where `hfin` is the explicit
finite-dimensionality proof for `W`.

| Declaration | Conclusion |
| --- | --- |
| `compactCompression_eventuallyStable` | `CompactCompressionEventuallyStable ρ hρ K hK g`, giving simultaneous stabilization of all sufficiently high power ranges and kernels. |
| `powerKernelSup_isCompl_stableImage` | `IsCompl (powerKernelSup ρ hρ K hK g) (stableImage ρ hρ K hK g)`. |
| `stableImageAction_bijective` | `Function.Bijective (stableImageAction ρ hρ K hK g)`. |
| `compactCompression_stabilizes_of_isAdmissible` | For arguments `ρ hAdm K hK g`, concludes `CompactCompressionStabilizes ρ hAdm.1 K hK g`. |

The first three are projections of the exact main theorem. The last applies it
as

```lean
compactCompression_stabilization ρ hAdm.1 K hK g (hAdm.2 K)
```

Here `hAdm.1` is smoothness and `hAdm.2 K` is finite generation of `W`.
Over `ℂ`, Mathlib's `FiniteDimensional` abbreviates `Module.Finite`, so this
is exactly the required dimension hypothesis. Compactness remains the
separately supplied witness `hK`.

## Derived provenance and scope

This is an internal specialization of Mathlib's finite-dimensional Fitting
theory to the published compact compression. It introduces no generic Fitting
construction. The range stabilization and complementary-submodule results
come from `Mathlib.RingTheory.Artinian.Module`; kernel stabilization comes from
`Mathlib.RingTheory.Noetherian.Defs`; the injective-surjective equivalence
comes from `Mathlib.LinearAlgebra.FiniteDimensional.Basic`. The source pin is
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The proof was developed by Worker 1 from Worker 1's earlier private probe.

The published statement's Markdown records the motivating comparison with
Casselman's Chapter III, section 5. The implemented proof uses the algebraic
Mathlib results described above and does not depend on Casselman's geometric
hypotheses. It proves precisely the three stated conclusions for the normalized
compression. It asserts no identification with a Jacquet quotient or Jacquet
relations, independence or multiplicativity in `g`, or pairing statement.
