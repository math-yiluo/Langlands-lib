# Stalks of étale sheaves on the spectrum of a field at two geometric points

Module `Langlands.Geometry.FieldEtaleStalkChange`, namespace
`Langlands.Geometry.FieldEtaleStalkChange`.

Let `K` be a field, `Ω` a separable closure of `K` (`[IsSepClosed Ω] [Algebra.IsSeparable K Ω]`),
`M` a separably closed field with a `K`-algebra structure, all in one universe `u`, and
`ι : Ω →ₐ[K] M`. A `K`-morphism `Spec M → X` to an étale `K`-scheme has image a point `p` of `X`
and corresponds to a `K`-embedding of the residue field `κ(p)` into `M`. Since `κ(p)` is finite
separable over `K`, its image consists of elements of `M` separable over `K`, hence over the
separably closed field `ι(Ω)`, so it lies in `ι(Ω)`. Thus every such morphism factors uniquely
through `Spec ι : Spec M → Spec Ω`. This is weil-conjectures's
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberIso` (with `exists_specAlgebraMap_comp_eq` and
`specMap_comp_injective`), applied to the `Ω`-algebra structure on `M` given by `ι`.

## Definitions and results

- `fiberIso K Ω M ι`: the isomorphism of fibre functors from the point
  `AlgebraicGeometry.Scheme.pointSmallEtale (Spec Ω → Spec K)` of the small étale site of
  `Spec K` to the point `pointSmallEtale (Spec M → Spec K)`, sending a lift `x` to the lift
  `Spec ι ≫ x` (`fiberIso_hom_app_left`).
- `pointIso K Ω M ι`: the corresponding isomorphism of points (weil-conjectures's
  `GrothendieckTopology.Point.isoMk`).
- `sheafFiberIso K Ω M ι A`: for every category `A` with colimits of size `u`, the induced
  isomorphism of the stalk functors on `A`-valued étale sheaves on `Spec K`
  (weil-conjectures's `GrothendieckTopology.Point.sheafFiberIso`).
- `toPresheafFiber_sheafFiberIso_hom_app`: `sheafFiberIso` sends the germ of a section at a lift
  `x` to its germ at `(fiberIso K Ω M ι).hom.app X x`, that is, at `Spec ι ≫ x`.

Applied with `M` a separable closure `Ω_L` of an extension `L` of `K` and a `K`-embedding
`ι : Ω → Ω_L`, this identifies the stalk at `Spec Ω → Spec K` with the stalk at
`Spec Ω_L → Spec L → Spec K`, as in the change-of-field clause of
`Langlands.Henniart.Laumon.FiniteEtaleFieldMonodromyStatement` (Stacks Project, Section 59.56).

## External declarations

From weil-conjectures: `AlgebraicGeometry.Scheme.pointSmallEtaleFiberIso`,
`AlgebraicGeometry.Scheme.specAlgebraMap`, `CategoryTheory.GrothendieckTopology.Point.isoMk`,
`CategoryTheory.GrothendieckTopology.Point.sheafFiberIso` and its germ lemma
`toPresheafFiber_sheafFiberIso_inv_app`. Every declaration of this module depends only on
`propext`, `Classical.choice` and `Quot.sound` under `#print axioms`.
