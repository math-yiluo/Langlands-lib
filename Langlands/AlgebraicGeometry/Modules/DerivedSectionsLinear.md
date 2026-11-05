# Base-linear action on actual relative cohomology

Let `X` be an actual scheme, `R` a commutative ring object, and
`p : X ⟶ Spec R`, all in arbitrary common universe `u`. Use the actual
`R`-linear category structure `Langlands.Scheme.Modules.linearOverBase p`:
a scalar acts on a sheaf morphism by multiplication by the corresponding
global function, restricted to each open subset.

`relativeGlobalSections_linear` proves that the existing functor
`relativeGlobalSections p` is linear for this specified action. On a global
section, the action is the one induced by
`Langlands.Scheme.Modules.scalarsFromBase p`. Restricting that global
function to the top open is the identity, so the two actions agree.
The theorem retains the specified category structure with a local `letI`;
it does not install a scalar structure independent of `p`.

`relativeCohomology_linear p n` then applies the generic
`Langlands.Cohomology.rightDerived_linear` construction to relative global
sections. Thus the actual right-derived relative cohomology functor is
`R`-linear for every nonnegative degree, without flatness, properness,
quasi-coherence or coefficient-acyclicity assumptions.

`relativeCohomologyHomLinearMap p n` packages the existing map on a sheaf
hom space as an `R`-linear map, using that same specified source-category
structure. `relativeCohomologyHomLinearMap_apply` identifies its value with
the existing relative cohomology map by definition.
`relativeCohomology_map_scalarHom` gives the instance-independent formula:
applying actual relative cohomology to
`scalarHom (scalarsFromBase p r) a` gives
`r • (relativeCohomology p n).map a`.
Its proof installs the specified category structure and its proved functor
linearity, then applies the scalar law.

The provenance is internal: this specializes the actual sheaf scalar action
and the resolution construction in `RightDerivedLinear`. It is a prerequisite
for comparing finite coefficient maps on Picard deformation cohomology.
It does not prove quotient tensor naturality, obstruction naturality, or the
field Picard-stack atlas theorem.
