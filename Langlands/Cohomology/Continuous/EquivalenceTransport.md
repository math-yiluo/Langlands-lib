# Continuous cohomology transport under equivalences

This internal construction transports Mathlib's actual continuous cohomology along a continuous group equivalence and a compatible isomorphism of topological representations. Its provenance is the identity and composition laws for `ContinuousCohomology.cochainsMap` in the pinned Mathlib module `Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality`.

All groups, the commutative coefficient ring, and coefficient carriers lie in an arbitrary common universe `u`. The group equivalence is `e : H ≃ₜ* G`; the coefficient input is `f : TopRep.res (e : H →ₜ* G) X ≅ Y`. No cohomology invertibility is assumed.

`transportInverseCoefficient e f` uses the continuous linear map underlying `f.inv`. Equivariance follows by applying the equivariance of `f.inv` at `e.symm g` and simplifying `e (e.symm g) = g`.

Both cochain composite identities follow from the actual cochain composition law. The composite group maps are identities, and the composite coefficient maps are identities by the two identities of `f`. The helper `continuousCochainsMap_congr` handles the dependent coefficient domains when the group maps are equal.

`continuousCochainsIso` packages these maps. `continuousCohomologyIso e f q` is an isomorphism in `TopModuleCat k` in every natural degree `q`; its inverse identities follow by applying homology to the proved cochain identities. Its forward map is definitionally `ContinuousCohomology.map (e : H →ₜ* G) f.hom q`, and its inverse is the map for `e.symm` and `transportInverseCoefficient e f`. The two named projection theorems record these exact equalities.

This is a generic construction with no arithmetic assumptions, and does not assert any comparison with a different model of continuous cohomology.
