# Ultrafilter lifting and spreading out of ultrapower points

Author: Worker 78.

Two auxiliary results, with internal provenance, for limits of rational points along
ultrafilters.

## Lifting ultrafilters to fibre products

`exists_ultrafilter_lift`: let `F : α → γ` and `D : β → γ` be maps, `γ` and `β` topological
spaces, and let a type `P` with maps `fst : P → α`, `snd : P → β` surject onto the
set-theoretic fibre product (`F a = D b` implies `a = fst p`, `b = snd p` for some `p`).
Suppose `D` sends neighbourhoods of `b₀` to neighbourhoods of `D b₀` (for instance `D` is an
open map) and `F` tends to `D b₀` along an ultrafilter `𝒰` on `α`. Then there is an
ultrafilter `𝒲` on `P` with `𝒲.map fst = 𝒰` and `snd` tending to `b₀` along `𝒲`.

Proof: the filter `comap fst 𝒰 ⊓ comap snd (𝓝 b₀)` is proper. For `A ∈ 𝒰` and a
neighbourhood `N` of `b₀`, `F⁻¹(D(N)) ∈ 𝒰`, so some `a ∈ A` has `F a = D b` with `b ∈ N`,
and a point of `P` over `(a, b)` lies in both sets. Any ultrafilter `𝒲` finer than it has
`map fst 𝒲 ≤ 𝒰`, hence equality, and `snd` tends to `b₀`.

## The ultrapower as a filtered colimit

Let `K` be a field, `𝒰` an ultrafilter on `I`, and `L` an `(I → K)`-algebra whose structure
map is surjective with kernel the families vanishing along `𝒰` (the ultrapower
`K^I/𝒰` is the example used). Write `vanishing K A` for the ideal of families vanishing on
`A ⊆ I`.

- `UltraIndex 𝒰` is the type of sets of `𝒰`, ordered by reverse inclusion; it is directed and
  nonempty, hence a filtered category.
- `stageDiagram K 𝒰` sends `A` to the `(I → K)`-algebra `(I → K) ⧸ vanishing K A` (which is
  `K^A`), with the quotient maps as transition maps.
- `stageCocone K 𝒰 hker` has vertex `L` and the maps `stageMap` induced by the structure map.
- `stageCoconeIsColimit` proves that this cocone is a colimit in `CommAlgCat (I → K)`. For a
  cocone `s`, the kernel of `I → K → L` is contained in that of `I → K → s.pt`
  (`ker_le_ker_of_cocone`: a family vanishing along `𝒰` vanishes on some `A ∈ 𝒰`, so it maps
  to zero through the stage `A`), and `stageDesc` is the induced map out of `L` (Mathlib's
  `RingHom.liftOfSurjective`). Factorization and uniqueness follow from surjectivity of
  `I → K → L`.
- `exists_stage_ringPoint`: every `L`-point of a scheme locally of finite presentation over
  `Spec (I → K)` comes from a point with values in some stage `(I → K) ⧸ vanishing K A`,
  `A ∈ 𝒰`. This is the Library's `filteredRingPointComparison` (filtered colimits of points
  of schemes locally of finite presentation) applied to the colimit above.
