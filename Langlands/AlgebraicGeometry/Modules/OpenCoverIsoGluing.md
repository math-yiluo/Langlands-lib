# Isomorphism gluing from unique gluing of module morphisms

`Langlands.Scheme.Modules.OpenCoverIsoGluingStatement.{u}` states unique
gluing of compatible actual module isomorphisms over any scheme open cover.
The theorem `openCoverIsoGluing_of_homGluing` derives this proposition from the
published `OpenCoverHomGluingStatement.{u}` as an explicit premise. This module
does not prove that premise or the host's unconditional Picard-zero theorem.

Let `X : Scheme.{u}`, let `𝒰 : X.OpenCover.{u}` have maps `uᵢ : Uᵢ → X`,
and let `M` and `N` be arbitrary sheaves of modules over the structure sheaf of
`X`. For every index, prescribe an actual isomorphism
`eᵢ : uᵢ* M ≅ uᵢ* N`. On `Uᵢ ×_X Uⱼ`, write `p₁` and `p₂` for the
projections and `α_A : p₁*(uᵢ* A) ≅ p₂*(uⱼ* A)` for the existing
`squarePullbackIso` comparison, for `A = M,N`.
The hypothesis is exactly the forward-map compatibility

```text
p₁*(eᵢ.hom) ≫ α_N.hom = α_M.hom ≫ p₂*(eⱼ.hom).
```

The conclusion is a unique actual global isomorphism `E : M ≅ N` such that
`uᵢ*(E.hom) = eᵢ.hom` for every index. Uniqueness is equality of
isomorphisms, rather than equality of isomorphism classes. The scheme, cover
index type in universe `u`, and modules are arbitrary. No reducedness,
quasi-separatedness, quasi-compactness, affineness, finiteness, quasi-coherence
or local-freeness hypothesis is imposed.

The implemented proof first glues the forward maps using the supplied
morphism-gluing proposition. Multiplying the compatibility equation by the
local inverse maps gives compatibility of the inverses with `M` and `N`
interchanged. Applying the same proposition glues those inverse maps. The two
global composites pull back to the respective identities on every member.
Unique gluing applied to each compatible family of local identity maps shows
that the global composites equal the identities. These two maps therefore
form an actual global isomorphism. Unique gluing of the forward maps, followed
by extensionality for isomorphisms, proves uniqueness.

This is an internal categorical corollary of the existing actual
module-morphism gluing interface, derived by functorial preservation of
isomorphisms and uniqueness. It is not a separately quoted literature result.
Worker 124 requested this focused corollary for the locally trivial
descent-uniqueness argument; the morphism-gluing proof remains separate work.
This module fixes the two global modules before prescribing local maps and
does not construct descent of module objects, rigidifications or Picard
classes.
