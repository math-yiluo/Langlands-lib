# Relative differentials for commutative squares and base change

For arbitrary schemes `X'`, `X`, `T`, and `S`, with maps `g : X' ⟶ X`,
`b : T ⟶ S`, `f' : X' ⟶ T`, `f : X ⟶ S` and commutativity
`w : g ≫ f = f' ≫ b`, `Langlands.Scheme.relativeDifferentialsSquareMap g b w`
is the canonical morphism
`(Scheme.Modules.pullback g).obj (relativeDifferentials f) ⟶ relativeDifferentials f'`.
All sheaves, universal derivations and functors are the actual published
constructions. Their universal property is proved in the imported
`RelativeDifferentialsUniversal` module, not assumed as an input.

`RelativeDerivation.forgetBase b d` converts an `f'`-relative derivation
into an `(f' ≫ b)`-relative derivation, retaining exactly the same local
additive maps, Leibniz rule and restriction compatibility. A base section
from `S` factors through the inverse-image open in `T`; the relative
vanishing property of `d` therefore proves the new base vanishing.
`forgetBase_app` gives the unchanged local formula and
`forgetBase_postcomp` proves compatibility with postcomposition.

Apply `forgetBase` to the universal derivation for `f'`, then the published
`precompOver g w` to obtain an `f`-relative derivation into the actual
pushforward of the target differential sheaf. Its universal descent is
`relativeDifferentialsSquarePushforwardMap g b w`. The inverse of the
actual pullback/pushforward adjunction defines the square map.
The `_fac` lemmas prove the derivation equations; `_adjoint` identifies
its adjoint with the descended map. `relativeDifferentialsSquareMap_adjoint_app`
shows on every open `U` of `X` and section `a` that this adjoint sends
`d_f(a)` to `d_f'(g.app U a)` on `g ⁻¹ᵁ U`.

`relativeDifferentialsSquareMap_unique` proves uniqueness from the
derivation equation using injectivity of the adjunction equivalence and
uniqueness for the universal derivation. `_unique_of_app` proves the same
uniqueness directly from the local-section formula by extensionality of
derivations.

`relativeDifferentialsSquareMap_id_base` proves agreement with the published
fixed-base `relativeDifferentialsMap` when the base map is the identity.
Its proof applies local uniqueness to the fixed-base map and uses its
published local-section formula.

`relativeDifferentialsBaseChangeMap f b` specializes the square map to
Mathlib's categorical scheme pullback, with `g = Limits.pullback.fst f b`
and `f' = Limits.pullback.snd f b`. Its local formula and local uniqueness
are `relativeDifferentialsBaseChangeMap_adjoint_app` and
`relativeDifferentialsBaseChangeMap_unique_of_app`. There are no smoothness,
flatness, or other geometric hypotheses. This file constructs the map;
it does not assert that it is an isomorphism.

## Provenance and sources

The construction and characterization implement Stacks Project
Lemma 29.33.8 (tag 01UV), in `01UM.html` of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
The forget-base helper is the explicit base-vanishing step in that lemma's
construction of an `S`-derivation. Its postcomposition lemma is a derived
local-map identity. Lemma 29.33.10 (tag 01V0) motivates the base-change
specialization; its isomorphism assertion is a separate theorem outside
this unit. The structure of the descent/adjunction API adapts Worker 136's
fixed-base `RelativeDifferentialsMaps` module, with the forget-base step
and explicit local uniqueness added here.

Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
`AlgebraicGeometry/Modules/Sheaf.lean` supplies the module adjunction;
`AlgebraicGeometry/Pullbacks.lean` supplies scheme pullbacks; and
`AlgebraicGeometry/Scheme.lean`, `Scheme.Hom.comp_app`, supplies the
local-section factorization for a composite morphism.
