# Group structure on scheme solutions along fppf covers

This module is the fppf analogue of the published module
`Langlands.GroupScheme.Descent.SchemeSolutionGroup`. All schemes lie in an
arbitrary universe `u`. Let `p : S ⟶ B` be surjective, flat and locally of
finite presentation, `G` an actual group scheme over `S`, `D : Datum p G` a
Čech datum, and `s : SchemeSolution D` a supplied underlying quotient. The
module builds an actual solution `s.fppfSolution : Solution D` whose
underlying object is `s.obj`. It assumes no affineness, quasi-compactness or
commutativity.

- `fppfSectionGroup U` moves the group structure of the compatible-section
  subgroup across `s.fppfSectionEquiv U` to the maps `U ⟶ s.obj`. The private
  lemmas `fppfLocalSection_one` and `fppfLocalSection_mul` identify its unit
  and product under restriction. Since restriction is injective and natural,
  precomposition preserves unit and product (`fppfSection_comp_one`,
  `fppfSection_comp_mul`).
- `fppfSectionPresheaf` is the resulting group-valued presheaf on `Over B`.
  `fppfSectionRepresentableBy` says that its underlying presheaf is
  represented by `s.obj` via the identity hom-set equivalence.
  `fppfGroupObj` is Mathlib's `GrpObj.ofRepresentableBy`, and
  `fppfGroupScheme` is `s.obj` with this group structure.
- `fppfIso_isMonHom`: the pullback comparison `s.iso.hom` preserves unit and
  multiplication. Restriction sends the reconstructed unit and multiplication
  to the local ones, and pulling back the reconstructed operations agrees with
  the monoidal comparison maps. `fppfGroupIso` bundles `s.iso` as an
  isomorphism of group schemes `(baseChange p).obj s.fppfGroupScheme ≅ G`; its
  underlying maps are `s.iso.hom` and `s.iso.inv`.
- `fppfCompatible_of_proj`: any homomorphism `e` that preserves the quotient
  projection is compatible with the canonical datum and `D`. Equality on the
  second pullback reduces, through the supplied pullback square, to equality
  over `S` and after `s.proj`. These follow from the slice equations, from
  relation invariance and from the formula for the canonical overlap.
  `fppfGroupIso_compatible` applies this to `fppfGroupIso`.
- `fppfSolution` packages the group scheme, the isomorphism and the
  compatibility as a `Solution D`.

Provenance is internal: these are the published étale arguments with the
section equivalence of `FppfSchemeSolutionSections`. There is no literature
assertion.
