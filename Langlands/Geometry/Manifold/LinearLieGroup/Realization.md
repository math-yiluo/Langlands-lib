# Closed linear realizations of Lie groups

`Langlands.Geometry.Manifold.LinearLieGroup.Realization`. The hypothesis under which results proved
for linear Lie groups with exponential charts (`IsExpLieAlgebra`) apply to a Lie group given in the
Library's notions, that is, with an arbitrary charted space and Mathlib's `LieGroup`. Namespace
`Langlands.LinearLieGroup`.

## The structure

`IsClosedLinearRealization I ρ`, for a group `G` with `[ChartedSpace H G]` modelled on
`I : ModelWithCorners ℝ E H` and a homomorphism `ρ : G →* 𝔸ˣ` into the units of a finite-dimensional
normed real algebra `𝔸`, has three fields:

- `isClosedEmbedding`: `ρ` is a closed topological embedding;
- `contMDiff_val`: `g ↦ (ρ g : 𝔸)` is smooth;
- `contMDiff_of_val`: for every `m`, a map `p : (Fin m → ℝ) → G` is smooth as soon as
  `x ↦ (ρ (p x) : 𝔸)` is smooth.

The third field is quantified over the spaces `Fin m → ℝ` only, so the structure has no universe
parameter beyond those of `G`, `E`, `H` and `𝔸`. This suffices because the charts of the image of
`ρ` are the globally defined maps `Y ↦ k exp Y` on a finite-dimensional Lie algebra, which after a
choice of basis is some `Fin m → ℝ`.

`isClosedLinearRealization_id`: the identity of `𝔸ˣ`, with Mathlib's manifold structure on the
units, is a closed linear realization (`contMDiff_units_of_contDiff_val` of `Units`).

## Transport to the image

For `hρ : IsClosedLinearRealization I ρ`:

- `isClosed_range`: `ρ.range` is closed in `𝔸ˣ`, so `isExpLieAlgebra : IsExpLieAlgebra ρ.range
  (lieSubmodule ρ.range _)` by the closed-subgroup theorem (`ClosedSubgroup`).
- `rangeEquiv : G ≃ₜ* ρ.range`: `ρ` corestricted to its image, an isomorphism of topological groups
  (the inverse is continuous because `ρ` is an embedding).
- `contMDiff_rangeRestrict_and_symm`: with the exponential charted space on the image
  (`letI := hρ.isExpLieAlgebra.chartedSpace`), `rangeEquiv` and its inverse are smooth. The first
  is `IsExpLieAlgebra.contMDiffAt_of_val` applied to `contMDiff_val`. For the second, smoothness at
  `k` of a map out of the image is smoothness at `0` of `Y ↦ f (k exp Y)`
  (`IsExpLieAlgebra.contMDiffAt_iff_expG_manifold`), and `Y ↦ ρ⁻¹ (k exp Y)`, read in a basis of the
  Lie algebra, is smooth by `contMDiff_of_val` since `ρ (ρ⁻¹ (k exp Y)) = k exp Y`.
- `contMDiff_iff_comp_symm`: `f : G → F` is smooth if and only if `f ∘ rangeEquiv.symm` is smooth
  for the exponential charts.

The exponential charted space on the image is installed locally; it never becomes an instance on a
type that already carries another charted space.

## Uses

`Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`
(`Langlands/Representation/Archimedean/DixmierMalliavin`) states the Dixmier–Malliavin theorem for
every Lie group with a closed linear realization. The archimedean points of the Library's reductive
group schemes have one (`Langlands.Global.InfiniteAdelicLinearRealization`), and so does `𝔸ˣ` with
`ρ = id`.

## Literature

Every closed subgroup of `GL_n(ℝ)` is a Lie group with the induced topology (the closed subgroup
theorem: B. C. Hall, *Lie groups, Lie algebras, and representations*, 2nd edition, GTM 222 (2015),
§3.8, Corollary 3.45, p. 70, proved on p. 71 from Theorem 3.42, p. 68). Hall states it for matrix
Lie groups, the closed subgroups of `GL(n; ℂ)` (Definition 1.4, p. 4), among which are the closed
subgroups of `GL_n(ℝ)`; the Library's `ClosedSubgroup` proves it for the units of a
finite-dimensional normed real algebra. The structure here packages what the transport needs; it
is not taken from a text.
