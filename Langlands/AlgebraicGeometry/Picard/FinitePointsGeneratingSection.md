# A global section generating a line bundle near a finite set of points

Module `Langlands.AlgebraicGeometry.Picard.FinitePointsGeneratingSection`, namespace
`Langlands.AlgebraicGeometry.Picard.FinitePointsGeneratingSection`.

Internal helper for the rigidification argument in the proof of
`FieldEtaleFppfClassSheafStatement`. All schemes are in an arbitrary universe `u`.

- `exists_basicOpen_separating`: on an affine scheme `Y`, if `y'` does not specialize to `y`,
  some global function `a` has `y ∈ D(a)` and `y' ∉ D(a)`. The complement of the closure of
  `y'` is an open neighbourhood of `y`, and basic opens form a basis (`isBasis_basicOpen`).
- `isUnit_add_of_nonunits`: in a local ring, a unit plus a non-unit is a unit.
- `exists_section_mem_trivializationOpen`: let `Y` be affine, `N` a line bundle on `Y` and `F`
  a finite set of points of `Y` no two of which specialize to each other. Then one global
  section `σ` of `N` has every point of `F` in its trivialization open
  (`trivializationOpen N σ`, the open where `σ` generates `N`).
  For each `y ∈ F` the published basis theorem `QuasiAffineSectionBasis.isBasis` gives a global
  section `s_y` generating near `y`. Products of separating functions give `e_y` with
  `y ∈ D(e_y)` and `y' ∉ D(e_y)` for the other points `y' ∈ F`. Put `σ = Σ e_y • s_y`. Near
  `y₀ ∈ F`, on the trivialization open `U` of `s_{y₀}`, every `s_y` is `c_y • s_{y₀}`
  (published `trivializesOn_iff_bijective` and `sectionHom_app`), with `c_{y₀} = 1`; hence `σ`
  is `r • s_{y₀}` with `r = Σ e_y c_y`. The published
  `inf_trivializationOpen_eq_basicOpen_of_res_eq_smul` identifies `U ∩ trivializationOpen σ`
  with `D(r)`, and the germ of `r` at `y₀` is a unit plus non-units, so `y₀ ∈ D(r)`.
- `exists_nbhd_le_trivializationOpen`: for a finite morphism `p : Y ⟶ T₀` from an affine
  scheme, a line bundle `N` on `Y` and a point `t` of `T₀`, there are an open neighbourhood `W`
  of `t` and a global section `σ` with `p⁻¹(W)` inside the trivialization open of `σ`. The
  fibre over `t` is finite and discrete (Mathlib `Scheme.Hom.finite_preimage_singleton`,
  `isDiscrete_preimage_singleton`), so no two of its points specialize to each other; the
  previous theorem gives `σ`; the image of the closed complement of its trivialization open is
  closed because finite morphisms are closed maps, and `W` is the complement of that image.
- `nonempty_pullback_iso_of_le_trivializationOpen`: pulling back `N` along any morphism whose
  range lies in the trivialization open of `σ` gives a module isomorphic to the structure
  sheaf. The morphism factors through the open subscheme (`IsOpenImmersion.lift`); the
  published `trivializationOpenIso`, Mathlib's `restrictFunctorIsoPullback` and the pullback
  comparisons give the isomorphism.

Provenance: internal; uses only published Library results on section loci and Mathlib.
