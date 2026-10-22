# Finite-dimensional stabilization of compact compressed actions

This module states the finite-dimensional Fitting decomposition for the actual
normalized compressed action from
`Langlands.Representation.Jacquet.CanonicalLiftDefinitions`. It contains
proposition definitions, not proofs of those propositions.

Let `G : Type uG` be a topological group and `V : Type uV` a complex module.
The universes `uG` and `uV` are independent. Fix a representation
`ρ : Representation ℂ G V`, its smoothness witness `hρ : Langlands.IsSmooth ρ`,
an open subgroup `K`, a compactness witness `hK : IsCompact (K : Set G)`,
and any `g : G`. Write

- `W = Langlands.fixedVectors ρ K.toSubgroup`;
- `C = Langlands.Jacquet.compressedAction ρ hρ K hK g`, an endomorphism of `W`;
- `S = Langlands.Jacquet.stableImage ρ hρ K hK g = ⨅ n : ℕ, range (C ^ n)`;
- `T = Langlands.Jacquet.powerKernelSup ρ hρ K hK g = ⨆ n : ℕ, ker (C ^ n)`.

These are the existing Library constructions. In particular, `C` acts by `g`
and then applies the normalized compact average, and the powers include
exponent zero. `stableImageAction ρ hρ K hK g` is the existing restriction of
`C` to the actual carrier of `S`.

All five new declarations are in the namespace `Langlands.Jacquet`:

| Declaration | Proposition |
| --- | --- |
| `CompactCompressionEventuallyStable ρ hρ K hK g` | There exists `r : ℕ` such that for every `s : ℕ` with `r ≤ s`, both `S = range (C ^ s)` and `T = ker (C ^ s)`. The same threshold works for both equalities. |
| `CompactCompressionSplits ρ hρ K hK g` | `IsCompl T S`, expressing that these submodules are disjoint and their supremum is all of `W`. |
| `CompactCompressionStableActionBijective ρ hρ K hK g` | `Function.Bijective (stableImageAction ρ hρ K hK g)`. |
| `CompactCompressionStabilizes ρ hρ K hK g` | The conjunction of the preceding three propositions, in that order. |
| `CompactCompressionStabilizationStatement` | Universally quantifies over `G`, its group and topological group structures, `V`, its additive group and complex module structures, and all of `ρ`, `hρ`, `K`, `hK`, `g`; assumes `FiniteDimensional ℂ W`; concludes `CompactCompressionStabilizes ρ hρ K hK g`. |

The first four declarations describe conclusions for fixed data without adding
a finite-dimensional premise. The selected final declaration supplies that
premise and binds all the data internally. Finite dimensionality is required
only of `W`, not of `V`. Zero fixed-vector spaces and zero representation
carriers are permitted; there is no `Nontrivial` assumption.

## Admissible specialization

The current definition in `Langlands.Representation.Smooth.Definitions` is

```lean
Langlands.IsAdmissible ρ =
  (Langlands.IsSmooth ρ ∧
    ∀ K : OpenSubgroup G, Module.Finite ℂ (Langlands.fixedVectors ρ K.toSubgroup))
```

Here the displayed equality describes the unfolding of the complex
specialization. If `hAdm : Langlands.IsAdmissible ρ`, then `hAdm.1` supplies
smoothness and `hAdm.2 K` supplies finite generation for every open subgroup,
including the chosen compact open `K`. Mathlib's `FiniteDimensional` is the
abbreviation for `Module.Finite` over a division ring, so the latter is exactly
the required premise over `ℂ`. Given a future proof
`h : Langlands.Jacquet.CompactCompressionStabilizationStatement`, the expression

```lean
h ρ hAdm.1 K hK g (hAdm.2 K)
```

has type `Langlands.Jacquet.CompactCompressionStabilizes ρ hAdm.1 K hK g`.
Compactness remains the separately supplied witness `hK`. This documents the
usable admissible specialization without postulating a second theorem.

## Derived provenance and scope

This is a derived specialization of ordinary finite-dimensional Fitting
decomposition to the published operator `C`. Finite dimensionality makes the
power ranges and kernels eventually stationary and complementary. On the
stable image, disjointness from the power-kernel supremum gives injectivity of
the restricted operator, and finite dimensionality then gives surjectivity.
These facts explain the statement's provenance; their proof is a separate task.
The eventual proof can reuse Mathlib's
`LinearMap.eventually_iInf_range_pow_eq`,
`LinearMap.eventually_iSup_ker_pow_eq`, and
`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`, in
`Mathlib.RingTheory.Artinian.Module` and
`Mathlib.RingTheory.Noetherian.Defs`. No new generic Fitting construction is
introduced here.

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
section 5, pages 5–7, especially III.5.4 and the paragraph following its proof
on page 6. Registered source: `casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
No project errata file for this source was present when this statement was
written.

Casselman uses admissibility, a compact open subgroup with Iwahori
factorization, and a contracting element in `A_P^{--}`. Page 5 defines `τ_a`
using an unnormalized sum over `K₀ a K₀ / K₀`. Page 6 discusses stationary
power kernels and, over a field, a stable complement on which `τ_a` is
invertible, given by a sufficiently high power image. Here the operator is
the normalized compact compression for arbitrary `g`, and the stable image
is defined as the intersection of all power ranges. Our statement isolates
the algebraic consequence, rather than transcribing the p-adic result.
Page 7's warning about an earlier incorrect general Noetherian-ring argument
for Jacquet admissibility does not furnish a general-ring extension here;
this statement is over `ℂ`.

There is no contraction, Iwahori factorization, GL rank, or Jacquet
admissibility hypothesis. The statement asserts neither bijectivity of
`stableImageJacquetMap`, independence or multiplicativity in `g`, equality
with Casselman's unnormalized operator, identification of `T` with Jacquet
relations, nor a pairing or duality conclusion. Those require separate
representation-theoretic work.
