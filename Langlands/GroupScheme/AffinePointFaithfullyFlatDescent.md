# Descent of points of a group scheme along faithfully flat algebra maps

Namespace `Langlands.GroupScheme.AffinePointDescent`. This module proves fpqc descent for the
points of a group scheme with values in algebras. It concerns a group scheme `G` over `Spec R`
for a commutative ring `R`, with its points `G.affinePoints T = (Spec T ⟶ G)` over `Spec R`
(module `Langlands.GroupScheme.AffinePoints`). Let `ι : T ⟶ T'` be a map of `R`-algebras whose
underlying ring map is faithfully flat. No affineness or finiteness hypothesis on `G` is needed.

## Content

- `algSpec_map_left`: the spectrum map of `ι` is `Spec.map ι`.
- `flat_surjective`, `epi_left`, `effectiveEpi_left`: `Spec T' → Spec T` is flat and
  surjective (Mathlib's `flat_and_surjective_SpecMap_iff`). It is therefore an epimorphism
  (`Flat.epi_of_flat_of_surjective`) and an effective epimorphism. The latter is Mathlib's
  instance for quasi-compact, surjective, flat morphisms, in `AlgebraicGeometry.Sites.Fpqc`.
- `affinePointMap_injective`: `G.affinePointMap ι : G(T) → G(T')` is injective, by cancelling
  the epimorphism.
- `square ι` is the tensor square `T' ⊗[T] T'` as an `R`-algebra. `inl ι` and `inr ι` are the
  two inclusions, and `comp_inl_eq_comp_inr` says that they agree on `T`.
- `exists_affinePointMap_eq` (**effective descent**): let `x' ∈ G(T')` be such that, for every
  `R`-algebra `Z` and all maps `a b : T' ⟶ Z` with `ι ≫ a = ι ≫ b`, the images of `x'` in
  `G(Z)` agree. Then `x'` is the image of some `x ∈ G(T)`.

  Proof. Any two morphisms `Z ⟶ Spec T'` that agree after `Spec T' → Spec T` factor through the
  fibre product. By Mathlib's `pullbackSpecIso`, that is `Spec (T' ⊗[T] T')` with the two
  projections induced by `inl` and `inr`. The hypothesis for `Z = square ι` therefore gives the
  cocycle condition for the underlying scheme map of `x'`. The effective epimorphism property
  then produces a morphism `Spec T → G`. It is a morphism over `Spec R` by cancelling the
  epimorphism.

The hypothesis is stated for all pairs `a, b` rather than only for the universal pair. Then
applications do not need to construct the tensor square.

## Provenance

This is faithfully flat (fpqc) descent of morphisms of schemes, as in the Stacks Project, Lemma
35.13.7 (Tag 023Q): representable functors are fpqc sheaves. The proof uses Mathlib's effective
epimorphism instance for quasi-compact, surjective, flat morphisms of schemes. The module is
internal infrastructure for the proof of `AffineWeilPairSingleChartDescentStatement`. There the
factor projection of a group is first defined over an étale cover and then descended.
