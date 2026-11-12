# Fixed vectors commute with extension of scalars

This module extends the scalars of a smooth representation that carries a
commuting group action. It proves that taking fixed vectors under a subgroup
commutes with this extension of scalars, compatibly with the second action. For
a Galois action it deduces that finiteness, continuity of orbits and
unramifiedness pass from `X^H` to `(M ⊗[K] X)^H`. All declarations are in
namespace `Langlands.Shimura.ScalarExtensionFixedVectors`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5, printed pp. 312-313, takes isotypic components of `λ`-adic
cohomology for automorphic representations whose coefficient field may be
larger than the `λ`-adic field `K_λ`. In this project such a component lives
in `(M ⊗[K_λ] X)`, where `X` is the tower cohomology over `K_λ` and `M` is a
field extension of `K_λ`. Its level-`H` part sits inside `(M ⊗[K_λ] X)^H`.
The properties of the Galois action are known at fixed level and over `K_λ`,
that is, on `X^H`. This module transports them to `(M ⊗[K_λ] X)^H`. The
results are generic: no Shimura variety appears.

## Definitions

`K` and `M` are fields with `Algebra K M`. `G` is a group with a topology, `Γ`
is a group, and `H : Subgroup G`.

- `extendScalarsActionFunctor M Γ :
  Action (SmoothRep K G) Γ ⥤ Action (SmoothRep M G) Γ` is the published
  extension of scalars of smooth representations
  `Langlands.Cohomology.smoothRepExtendScalars K M G`, applied to objects with
  a commuting `Γ`-action (`Functor.mapAction`). The space of the image of `X`
  is `M ⊗[K] X`. Both `g ∈ G` and `γ ∈ Γ` act on the second factor
  (`extendScalarsActionFunctor_obj_representation_tmul`,
  `extendScalarsActionFunctor_obj_ρ_tmul`).
- `fixedVectorsBaseChange M Γ X H :
  M ⊗[K] X^H →ₗ[M] (M ⊗[K] X)^H` is the base change of the inclusion
  `X^H → X`, `m ⊗ x ↦ m ⊗ x`, with its values in the `H`-fixed vectors
  (`baseChange_subtype_mem_fixedVectors`). Here `X^H` is
  `fixedVectors X.V.representation H`.
- `fixedVectorsBaseChangeEquiv M Γ X H` is this map as a linear equivalence.
- `fixedVectorsBaseChangeIso M X H`, for `Γ = Field.absoluteGaloisGroup F`, is
  an isomorphism of Galois actions. Its source is the extension of scalars
  `LatticeGaloisRepresentation.baseChangeAction (L := M)` of the Galois action
  on `X^H` (`fixedVectorsActionFunctor K Γ H`). Its target is the Galois action
  on `(M ⊗[K] X)^H` (`fixedVectorsActionFunctor M Γ H`). Its underlying map is
  `fixedVectorsBaseChange` (`fixedVectorsBaseChangeIso_hom_hom`).

## Results

- `fixedVectorsBaseChange_injective` and `fixedVectorsBaseChange_surjective`:
  the map `M ⊗[K] X^H → (M ⊗[K] X)^H` is bijective.
- `fixedVectorsBaseChange_comm`: the map commutes with the action of each
  `γ ∈ Γ`.
- `finite_fixedVectors_extendScalars`: if `X^H` is finite-dimensional over `K`,
  then `(M ⊗[K] X)^H` is finite-dimensional over `M`.
- `hasContinuousOrbits_fixedVectors_extendScalars hKM hX`: suppose `K` and `M`
  carry topologies with `algebraMap K M` continuous (`hKM`). If the Galois action
  on `X^H` has continuous orbit maps
  (`ContinuousGaloisAction.HasContinuousOrbits`, module topology over `K`), then
  so does the Galois action on `(M ⊗[K] X)^H` (module topology over `M`).
- `isUnramifiedAlong_fixedVectors_extendScalars hu` and
  `isUnramifiedAt_fixedVectors_extendScalars hu`: for a number field `F` and a
  finite place `v`, unramifiedness of the Galois action on `X^H` at `v` (along
  a closure embedding `ι`, or along Mathlib's chosen one) implies the same for
  `(M ⊗[K] X)^H`.

No hypothesis on the topology of `M` beyond continuity of `K → M` is used. In
particular every topology on `M` that extends that of `K` qualifies.

## Proof outline

- Injectivity: `M` is free, hence flat, over the field `K`. So the base change
  `id_M ⊗ ι` of the injective inclusion `ι : X^H → X` is injective
  (`Module.Flat.lTensor_preserves_injective_linearMap`).
- Surjectivity: choose a basis `(b_i)` of `M` over `K`. Then every `t ∈ M ⊗[K] X`
  is uniquely `∑ b_i ⊗ x_i`, with the coefficients given by
  `TensorProduct.equivFinsuppOfBasisLeft`. An element `h ∈ H` acts by
  `id ⊗ h`, so the coefficients of `h · t` are the `h · x_i`. If `t` is
  `H`-fixed, uniqueness gives `h · x_i = x_i` for all `h ∈ H`. So each `x_i` lies
  in `X^H`, and `t` is the image of `∑ b_i ⊗ x_i ∈ M ⊗[K] X^H`.
- Equivariance holds on pure tensors by definition, and in general by additivity.
- The transfers apply the results of `Langlands.Shimura.ContinuousOrbitTransfer`
  and `Langlands.Shimura.LatticeGaloisRepresentation`. The extension of scalars
  of the action on `X^H` has continuous orbits
  (`hasContinuousOrbits_baseChangeAction`) and is unramified wherever `X^H` is
  (`isUnramifiedAlong_baseChange`). Both properties pass along the surjective
  equivariant map `fixedVectorsBaseChange`
  (`hasContinuousOrbits_of_surjective`, `isUnramifiedAlong_of_surjective`).

## Provenance

That invariants commute with flat base change, here along a field extension, is
standard linear algebra. The module supports the `λ`-adic isotypic components
of Harris (1999), §5, printed pp. 312-313, with coefficients extended from
`K_λ` to a larger field. No statement of Harris is formalized here.
