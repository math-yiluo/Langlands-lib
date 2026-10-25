# Coefficient and geometric coherence for sheafified scalar extension

## Scope and inputs

This module constructs the mixed comparison between composite coefficient
extension and geometric pullback, and proves that the coefficient identity and
composition comparisons commute with the geometric comparison. It treats both
ordinary small-etale module sheaves and geometric equivariant sheaves.

The coefficient rings `R`, `A`, and `B` are arbitrary commutative rings in
`Type u`, with unital ring maps `φ : R →+* A` and `ψ : A →+* B`.
The schemes `X` and `Y` and the module carriers use the same universe `u`.
The scheme morphism `f : Y ⟶ X` is etale. For the equivariant constructions,
`G : Type w` is an abstract group in an independent universe. The actions are
`ρ : G →* (Aut X)ᵐᵒᵖ` and `τ : G →* (Aut Y)ᵐᵒᵖ`, with the supplied
geometric equivariance equation

```text
f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f
```

for every `g`. There is no topology or smoothness assumption on `G`.

The imported coefficient extension is the actual sectionwise module tensor
functor followed by sheafification on the scheme's small-etale site. Pullback
here is the restriction functor associated to the etale map. The identity and
composition comparisons are the already constructed adjoint mates of the
inverse scalar-restriction comparisons. None of these functors or comparisons
is supplied as desired result data.

## Provenance

This is an internal categorical construction. It builds on
`EtaleScalarExtensionPullback`, `EtaleScalarExtensionCoherence`, and their
geometric equivariant versions, imported through
`EtaleEquivariantScalarExtensionPullback` and
`EtaleEquivariantScalarExtensionCoherence`. The proof uses the constructed
extension/restriction adjunction, its unit equations, and naturality. No external
literature theorem is being transcribed. These are intrinsic compatibility laws
for the coefficient and geometric constructions used by the Harris framework;
they do not identify those general constructions with a particular Harris
coefficient system.

## Ordinary sheaf comparisons

Write `L_φ^X` for `sheafExtendScalars φ X`, `U_φ^X` for scalar restriction,
and `P_R` for `restriction f (ModuleCat R)`. The existing geometric comparison
has direction

```text
β_φ(F) : P_A(L_φ^X F) ≅ L_φ^Y(P_R F).
```

Write `c_X(F)` for the forward component of
`sheafExtendScalarsCompIso φ ψ X`, from `L_(ψ.comp φ)^X F` to
`L_ψ^X(L_φ^X F)`, and `i_X(F)` for the forward identity-extension
comparison. Composition below uses Lean's left-to-right notation `≫`.

`sheafExtendScalarsPullbackIso_ring_id` proves

```text
β_id(F).hom ≫ i_Y(P_R F) = P_R.map(i_X(F)).
```

`sheafExtendScalarsPullbackIso_ring_comp` proves

```text
β_(ψ.comp φ)(F).hom ≫ c_Y(P_R F)
  = P_B.map(c_X(F)) ≫ β_ψ(L_φ^X F).hom ≫ L_ψ^Y.map(β_φ(F).hom).
```

Both routes therefore start at `P_B(L_(ψ.comp φ)^X F)` and end at
`L_ψ^Y(L_φ^Y(P_R F))`.

`sheafExtendScalarsCompPullbackIso` packages the left route as a natural
isomorphism

```text
L_(ψ.comp φ)^X ⋙ P_B ≅ P_R ⋙ (L_φ^Y ⋙ L_ψ^Y).
```

It is the geometric comparison followed by the left whiskering of the
coefficient-composition comparison by `P_R`. Its inverse and naturality are
inherited from this composition of natural isomorphisms.
`sheafExtendScalarsCompPullbackIso_hom_app` identifies its forward component
with the right route displayed above.

## Proof of the ordinary coherence laws

`sheafExtensionPullback_unit_hom_ext` states that two `A`-linear sheaf maps
from `P_A(L_φ^X F)` to an `A`-sheaf `E` agree if their scalar restrictions
agree after precomposition with `P_R.map(η_φ^X(F))`. The proof precomposes
both maps with `β_φ(F).inv`, applies injectivity of the extension/restriction
hom equivalence over `Y`, and uses the geometric unit equation. Composing back
with `β_φ(F).hom` cancels the isomorphism.

For the identity square, this extensionality reduces the claim to the identity
unit equation over `X` pulled back to `Y` and the corresponding equation over
`Y`. Evaluation at every etale object and section identifies the scalar
restriction identity maps.

`sheafExtensionUnit_comp_pullback` transports the coefficient-composition
unit equation over `X` along geometric restriction. With `s_Y` the scalar
restriction composition isomorphism, it says

```text
P_R.map(η_(ψ.comp φ)^X(F)) ≫ U_(ψ.comp φ)^Y.map(P_B.map(c_X(F)))
  = P_R.map(η_φ^X(F))
      ≫ U_φ^Y.map(P_A.map(η_ψ^X(L_φ^X F)))
      ≫ s_Y.inv.app(P_B(L_ψ^X(L_φ^X F))).
```

The proof evaluates the existing equation over `X` at the image of each etale
object over `Y`. The restriction-composition map is the same module map on
sections.

For the composition square, unit extensionality first reduces the left route to
the composite unit equation over `Y`. The transported equation rewrites the
right route. Naturality of the inverse scalar restriction composition
comparison moves it past the two geometric maps. The geometric unit equation
for `ψ`, naturality of its unit at `β_φ(F).hom`, and the geometric unit
equation for `φ` reduce the resulting expression to the left route. The proof
uses ordinary associativity and functoriality; it assumes no extra compatibility.

## Equivariant comparisons

`scalarExtensionEquivariantPullbackIso_ring_id` and
`scalarExtensionEquivariantPullbackIso_ring_comp` prove the same two equations
in the categories `EquivariantSheaf R ρ` and `EquivariantSheaf R τ`, with
`equivariantPullback` and `scalarExtensionFunctor` in place of their ordinary
versions. The maps already have their equivariance fields. Faithfulness of
forgetting those fields reduces each equality to the ordinary law above.

`scalarExtensionCompEquivariantPullbackIso` is the natural isomorphism

```text
scalarExtensionFunctor (ψ.comp φ) ρ ⋙ equivariantPullback B ρ τ f hf
  ≅ equivariantPullback R ρ τ f hf
      ⋙ (scalarExtensionFunctor φ τ ⋙ scalarExtensionFunctor ψ τ).
```

It is constructed by composing the existing equivariant geometric comparison
with the whiskered equivariant coefficient-composition comparison.
`scalarExtensionCompEquivariantPullbackIso_hom_app` gives its two-step formula.
`scalarExtensionCompEquivariantPullbackIso_hom_app_hom` shows that forgetting
equivariance gives the forward ordinary mixed comparison definitionally.

## Limits

These constructions assert coefficient identity/composition compatibility with
etale restriction. They do not establish flatness, exactness, smoothness,
preservation of injectives, commutation with sections or higher cohomology,
compact-support comparisons, or inverse-limit comparisons. Ideal reduction,
coefficient inverse systems, and actual Harris/Shimura specialization remain
separate work. The module does not claim completion of the full Harris
geometric and cohomological framework.
