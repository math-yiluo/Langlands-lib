# Scalar extension preserves bounded-above flat quasi-isomorphisms

Module `Langlands.Cohomology.ModuleComplex.FlatQuasiIsoBaseChange`.

## Main result

`quasiIso_baseChange_map_of_flat φ u b hK hL`. Let
`φ : R →+* S` be any homomorphism of commutative rings in universe `u`. Let
`u : K ⟶ L` be a quasi-isomorphism of `ℤ`-indexed cochain complexes of
`R`-modules. Suppose both complexes are strictly bounded above by the same
integer `b` (`[K.IsStrictlyLE b] [L.IsStrictlyLE b]`, so every term in a degree
`> b` is zero) and every term `K.X n`, `L.X n` is a flat `R`-module. Then the
degreewise scalar extension `(baseChange φ).map u` is a quasi-isomorphism of
complexes of `S`-modules. Here `baseChange φ` is the Library functor
`Langlands.Cohomology.ModuleComplex.baseChange`, which applies
`ModuleCat.extendScalars φ` termwise.

The complexes need not be bounded below, and `φ` need not be flat.

## Auxiliary declarations

- `quasiIso_iff_exactAt_mappingCone`: in an abelian category, a
  morphism of `ℤ`-indexed cochain complexes is a quasi-isomorphism iff its
  mapping cone is exact in every degree. This uses Mathlib's distinguished
  mapping-cone triangle in the homotopy category and the description of
  quasi-isomorphisms as the morphisms whose cone is acyclic.
- `exists_d_eq_of_exactAt`: the element form of exactness at
  degree `n + 1` for a complex of modules.
- `cocycleSubmodule E n`: the kernel of the differential leaving
  degree `n`. `d_d_apply` is `d ∘ d = 0` on elements.
  `toCocycleSubmodule E n` is the differential leaving degree `n`,
  with codomain restricted to the cocycles of degree `n + 1`.
- `cocycleSubmodule_subtype_comp_toCocycleSubmodule` and
  `exact_cocycleSubmodule_subtype` say that the inclusion of the
  cocycles followed by the restricted differential is exact, and that composing
  the restricted differential with the inclusion recovers the differential.
- `toCocycleSubmodule_surjective`: if the complex is exact in
  every degree, then every restricted differential is surjective.
- `flat_cocycleSubmodule`: if `E` is exact in every degree,
  strictly bounded above by `b`, and has flat terms, then every module of
  cocycles is flat. Above `b` the cocycle module is a submodule of the zero
  module. Going down one degree uses the short exact sequence
  `0 → Z^m → E^m → Z^{m+1} → 0` and the published Library theorem
  `Module.Flat.ker_of_surjective_of_flat`: the kernel of a surjection between
  flat modules is flat. Induction on `b + 1 - m` finishes the proof.
- `exists_lTensor_d_eq`: under the same hypotheses, for every
  `R`-module `A` the complex `A ⊗ E` is exact, in element form at degree
  `n + 1`. Since `Z^{n+3}` is flat, tensoring the short exact sequence
  `0 → Z^{n+2} → E^{n+2} → Z^{n+3} → 0` with `A` keeps the first map injective
  (`LinearMap.lTensor_injective_of_exact_of_flat`). A cocycle of `A ⊗ E^{n+1}`
  therefore lies in the kernel of `A ⊗ (E^{n+1} → Z^{n+2})`. By right exactness
  (`lTensor_exact`) it comes from `A ⊗ Z^{n+1}`, and `A ⊗ E^n → A ⊗ Z^{n+1}`
  is surjective.
- `exactAt_baseChange_of_flat`: the same statement for
  `(baseChange φ).obj E`. On elements, the differentials of the scalar extension
  are `lTensor` with `S`, viewed as an `R`-module through `φ`, so this is the
  case `A = S` of `exists_lTensor_d_eq`.
- `flat_mappingCone_X`: the mapping cone of a morphism of
  complexes with flat terms has flat terms. Degree `n` of the cone is the
  biproduct `K.X (n + 1) ⊞ L.X n`, which is isomorphic to the product. Product
  flatness reuses the published
  `P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat.QisoBC.flat_prod`;
  this module adds no duplicate product-flatness helper.
- `mappingCone_isStrictlyLE`: the mapping cone of a morphism
  between complexes strictly bounded above by `b` is strictly bounded above by
  `b`.

## Proof of the main result

Since `u` is a quasi-isomorphism, its mapping cone is exact in every degree. It
has flat terms and is strictly bounded above by `b`, so by
`exactAt_baseChange_of_flat` its scalar extension is exact in every degree.
Scalar extension is an additive functor; the Library instance
`extendScalars_additive` from `Langlands.Cohomology.PerfectModuleComplexHomotopy`
supplies this. So Mathlib's `CochainComplex.mappingCone.mapHomologicalComplexIso`
identifies the scalar extension of the cone with the cone of
`(baseChange φ).map u`. That cone is therefore exact in every degree, and
`quasiIso_iff_exactAt_mappingCone` gives the conclusion.

## Provenance

This is internal infrastructure, not a translation of a single cited result.
The argument is the standard one: a bounded-above acyclic complex of flat
modules has flat cocycle modules, so it stays acyclic after any tensor product,
and quasi-isomorphisms are detected by their cones. The Library already proves
a related unbundled result for `ℕ`-indexed complexes concentrated in degrees
`0, …, n` and algebra base changes
(`BoundedFlatQuasiIsoBaseChangeStatement`). The present module is stated for
the categorical `ℤ`-indexed complexes and the functor `baseChange φ` used by the
perfect-complex and Čech base-change developments, and needs no lower bound. It
is the algebraic input for comparing the scalar extension of a Čech complex with
a strictly perfect model over another base.
