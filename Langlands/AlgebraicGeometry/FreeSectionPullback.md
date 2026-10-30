# Pulling finite free section bases back

This internal prerequisite constructs section bases from a supplied global
finite free trivialization and proves their compatibility with the actual
pullback of module sheaves. It then transports matrices and the universal
determinant polynomial in these constructed bases.

All declarations are in `Langlands.Scheme.Modules`. Let `X` and `Y` be actual
Mathlib schemes in the same universe, let `M` be an `O_X`-module sheaf, and let
`I` be a finite type in that universe. The input trivialization is an actual
sheaf isomorphism

`e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M`.

For a scheme morphism `f : Y ⟶ X` and any open `U` of `X`, the coefficient map
is the ring homomorphism `(f.app U).hom`, from sections on `U` to sections on
`f ⁻¹ᵁ U`. No affine-open hypothesis is imposed.

`globalFreeOverIso e U` constructs the corresponding trivialization on the
over-site of `U`. The restriction functor is additive, so it preserves the
finite coproduct defining the finite free sheaf. The construction uses Mathlib's
`SheafOfModules.mapFreeIso`, with the identity comparison on the structure
module, followed by the restriction of `e`.

`globalSectionBasis e U` evaluates the published `localSectionBasis` construction
for this over-site trivialization at `Over.mk (𝟙 U)`. It is a genuine
`Module.Basis I Γ(X, U) Γ(M, U)`. The theorem
`globalSectionBasis_apply` identifies its `i`th vector with `e.hom` applied to
the canonical free section indexed by `i`, evaluated on `U`. Its proof evaluates
Mathlib's coproduct-generator comparison at the section `1`.

`freePullbackIso f I` specializes Mathlib's
`SheafOfModules.pullbackObjFreeIso` to the actual morphism of ringed sites
associated to `f`. Its direction is from the pullback of the free sheaf on `X`
to the free sheaf on `Y`. This comparison and its generator theorem work for
arbitrary `I` in the indicated universe; finiteness is needed for the section
basis construction.

`globalFreePullbackIso f e` constructs a trivialization of the actual sheaf
`(Scheme.Modules.pullback f).obj M`. Its direction is from the free sheaf on
`Y` to that pullback: it first uses the inverse of `freePullbackIso`, then the
actual pullback functor applied to `e`.

`sectionPullback_freeSection` proves that `freePullbackIso.hom` sends the
actual unit-induced pullback of a free generator on `U` to the free generator
on `f ⁻¹ᵁ U`. The proof uses naturality of the pullback-pushforward adjunction
unit with respect to the coproduct inclusion `ιFree i`, and Mathlib's equation
relating that inclusion to `pullbackObjFreeIso`. The structure-module comparison
is adjoint to the structure morphism of ringed sites. Evaluating this morphism
equality at `1` gives the section identity, because the coefficient ring
homomorphism preserves `1`.

`sectionPullback_globalSectionBasis` consequently proves

`sectionPullback f M U (globalSectionBasis e U i) =
 globalSectionBasis (globalFreePullbackIso f e) (f ⁻¹ᵁ U) i`.

It first applies the inverse free-sheaf comparison to the free-generator identity,
then uses naturality of the actual section map with respect to `e.hom` and the
proved formula for each basis vector. Thus the target basis and the
compatibility equation are constructed from `e` and `f`.

`globalSectionBasis_pullback_toMatrix` says that the matrix of an actual sheaf
endomorphism `a : End M` in the source basis, mapped entry by entry by
`(f.app U).hom`, equals the matrix of its actual pullback in the constructed
target basis. `globalSectionBasis_pullback_determinant` gives the corresponding
equality of multivariate polynomials for any finite family `a : ι → End M`.
The polynomial is the existing `Langlands.Shimura.HodgeDeterminant.polynomial`,
the determinant of the universal linear combination of the endomorphism
matrices. Both results specialize the published section-pullback transport
theorems, using the compatibility equation just proved. The polynomial identity
holds over the actual commutative rings of sections, including rings with
nilpotents; flatness and reducedness are not required.

The provenance is an internal derivation from the published section and local
basis APIs and Mathlib's free-sheaf pullback comparison, rather than a translation
of a literature theorem. The input global trivialization remains explicit.
This unit does not construct local chart comparisons for a sheaf supplied only
with local trivializations, identify any abelian scheme's Lie module after
base change, or prove the Harris PEL determinant condition. Those geometric
specializations remain separate obligations.
