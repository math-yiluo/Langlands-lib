# Ordered Čech cochains over all tuples compute actual cohomology

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCohomology`,
namespace `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`.

## Purpose

`CechResolution.AllSeq` (module `...CechResolution.AllSeq`) builds the
sheafified ordered Čech complex `complex U M` over all tuples and proves that it
resolves `M`. This module takes `R`-module global sections. It identifies them
with explicit ordered Čech cochains and concludes that their cohomology is the
actual cohomology `(relativeCohomology π n).obj M`. It mirrors the Library's
alternating versions `CechResolution.Comparison` and
`CechResolution.cechCohomologyIso`.

## Setting

`π : X ⟶ Spec R` is a scheme over an affine base, `ι : Type u` is a `Fintype`,
`U : ι → X.Opens`, and `M : X.Modules`.

## Definitions

- `cochain π U M p` is the `R`-module of families
  `σ ↦ c σ ∈ (OModulePresheaf.ofModules π M).obj (inter U σ)`, indexed by all
  `σ : Fin (p + 1) → ι`. The underlying type of each factor is `Γ(M, inter U σ)`.
  The `R`-module structure is that of `OModulePresheaf.ofModules π M`, the same
  one used by the Library's alternating `cechCochainComplex`.
- `dCochain π U M p : cochain π U M p →ₗ[R] cochain π U M (p + 1)` is the ordered
  Čech differential. `dCochain_apply` gives
  `dCochain c τ = ∑ j, (-1)^j • res (c (τ ∘ j.succAbove))`.
- `cochainComplex π U M : CochainComplex (ModuleCat R) ℕ` is built from these
  modules and differentials. `cochainComplex_d` records its differential.
- `toCochainFun U M x σ` restricts the `σ`-component of a global section `x` of
  `term U M p` from `inter U σ ⊓ ⊤` to `inter U σ`. `toCochain π U M p` is the
  same map as an `R`-linear map. `sectionsIso π U M p` is the induced isomorphism
  `(relativeGlobalSections π).obj (term U M p) ≅ ModuleCat.of R (cochain π U M p)`.
- `sectionsComplexIso π U M` is the isomorphism of complexes
  `Γ_R(complex U M) ≅ cochainComplex π U M`.
- `cohomologyIso π U M hU hUa n` is the isomorphism
  `(cochainComplex π U M).homology n ≅ (relativeCohomology π n).obj M`. It is
  cohomology of `sectionsComplexIso.symm`, followed by the comparison map
  `resolutionComparison (relativeGlobalSections π) (aug U M) n`.

## Main results

- `isAffineOpen_inter π hAff σ`: if `π` is separated and every `U i` is affine,
  then every `inter U σ` is affine. Finite intersections of affine opens are
  affine over a separated base (`isAffineOpen_inf`), and `Fin (p + 1)` is
  nonempty.
- `isZero_relativeCohomology_term π hAff M p n`: for quasi-coherent `M`, the
  higher `R`-module cohomology of each term `term U M p` vanishes. Each summand
  `sheafOn M (inter U σ)` is acyclic by the Library's
  `isZero_relativeCohomology_sheafOn`. A finite biproduct of acyclic modules is
  acyclic by `isZero_obj_biproduct` and `rightDerived_additive`.
- `dCochain_toCochainFun`: `toCochainFun` intertwines the sheaf differential
  `d U M p` with `dCochain`. `dCochain_comp_dCochain` deduces `d ∘ d = 0` on
  cochains from the sheaf-level `d_comp_d`, since `toCochainFun` is surjective.
- `isIso_resolutionComparison_aug`: assume `π` is separated, `M` is
  quasi-coherent, `hU : ⨆ i, U i = ⊤`, and `hUa : ∀ i, IsAffineOpen (U i)`.
  Then `resolutionComparison (relativeGlobalSections π) (aug U M) n` is an
  isomorphism for every `n`. This combines `quasiIso_aug` with the Library's
  `acyclicResolutionComparisonStatement`.
- `cohomologyIso` is defined from these results.

## Proof notes

`toCochainFun_injective` and `toCochainFun_surjective` use that `toSec` is a
bijection, together with the two-way restriction between `inter U σ ⊓ ⊤` and
`inter U σ` (`map_map_of_le_of_le`). `toCochain` is `R`-linear by
`toCochainFun_smul` and `structureRingHom_comp_inter`. These compare the scalar
action through `relativeGlobalSections π` with the one of
`OModulePresheaf.ofModules π M`. The arguments are those of the Library's
`CechResolution.Comparison`, with strictly increasing tuples replaced by all
tuples.

## Provenance

This is internal infrastructure: the acyclic-resolution computation of
derived functors, applied to the ordered Čech resolution. It uses only Library
declarations and Mathlib.
