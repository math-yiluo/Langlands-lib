# Global representations from local finite linear models

This is an internal adapter between the published `FiniteLinearModels`
interface and the open-cover representation and property-descent constructions
in `AlgebraicSpace.LocalRepresentationProperties`. It supplies no geometric
finite-model existence theorem.

Fix a scheme `B` in universe `u` and a presheaf `F` on the entire slice
`Over B` with values in `Type (u + 1)`.
`HasLocalModels.exists_affine_representation` assumes that `F` is an fppf
sheaf and satisfies `FiniteLinearEquations.HasLocalModels`. It produces an
actual `V : Over B`, a natural isomorphism from the lifted represented
presheaf of `V` to `F`, and the properties `IsAffineHom V.hom` and
`LocallyOfFinitePresentation V.hom` of that same structure map.

The proof first invokes `HasLocalModels.exists_local_representations`,
which gives a pointwise covering family of open immersions from actual
affine spectra and, on each member, a full-slice representative with both
morphism properties. It packages the given open immersions and covering
condition as an actual `Scheme.OpenCover` indexed in `Type u`, chooses the
local natural representation isomorphisms, and invokes
`LocalRepresentation.exists_affine_representation` with the explicit fppf
sheaf premise. The latter theorem glues the scheme representatives and
transfers the two properties from their actual base changes.

`HasLocalModels.representation` chooses data from this existence result.
It returns a dependent pair whose first component is `V : Over B` and whose
second component is a natural representation isomorphism together with the
two properties, expressed as a subtype. This is noncomputable choice from
a proved existence theorem.

Both premises remain explicit: the actual proper coherent-family Hom
presheaf must still be proved to be an fppf sheaf and to have local finite
linear models. All tests and arrows in the slice and the explicit lifted
value universe are retained throughout the representation comparison.
