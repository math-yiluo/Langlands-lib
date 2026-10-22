# Ext in the category of smooth representations

Author: Worker 13.

This module defines `Ext^n(V, W)` for smooth representations `V` and `W` as
the `n`-th right derived functor of equivariant Hom out of `V`, evaluated at
`W`, in the abelian category `Langlands.SmoothRep R G`. The abelian structure
and enough injectives come from the companion modules
`Representation/Category/Abelian` and
`Representation/Category/SmoothPartAdjunction`. Equivariant Hom is the
published `SmoothHomComplex.homFunctor`, Mathlib's linear coyoneda.

## Mathematical content

Let `R` be a commutative ring and `G` a topological group, both in one
universe `u`; representation carriers are also in `u`. This is the universe
in which the companion module proves enough injectives.

- `homFunctorForgetIso R G V`: after forgetting module structure,
  `homFunctor R G V` is Mathlib's ordinary coyoneda functor `Hom(V, -)`.
- `homFunctor_preservesFiniteLimits`: `Hom(V, -)` with module values is left
  exact. The coyoneda functor preserves limits, and the forgetful functor of
  modules preserves and reflects finite limits.
- `ext R G V n : SmoothRep R G ⥤ ModuleCat R` is
  `(homFunctor R G V).rightDerived n`, Mathlib's right derived functor,
  computed with chosen injective resolutions of the second argument.
- `extMap R G f n : ext R G W n ⟶ ext R G V n` for `f : V ⟶ W` is the right
  derived natural transformation of precomposition with `f`. `extMap_id` and
  `extMap_comp` prove its contravariant functoriality.
- `bifunctor R G n : (SmoothRep R G)ᵒᵖ ⥤ SmoothRep R G ⥤ ModuleCat R` is
  the degree `n` Ext bifunctor, contravariant in the first argument.
- `isoHomologyOfInjectiveResolution R G V I n`: for any injective resolution
  `I` of `W` in the smooth category, `Ext^n(V, W)` is isomorphic to the
  degree `n` cohomology of `Hom(V, I)`. This is Mathlib's
  `InjectiveResolution.isoRightDerivedObj`.
- `extZeroIso R G V`: in degree zero, Ext is equivariant Hom, by left
  exactness and Mathlib's `rightDerivedZeroIsoSelf`.
- `isZero_ext_succ_of_injective`: Ext vanishes in positive degrees when the
  second argument is injective in the smooth category.

The derived functor is taken in the second variable. No balancing statement
comparing it with resolutions of the first argument, and no comparison with
Hom out of a projective complex, is claimed here. Harris's proof of
Proposition 4.4 (printed p.310) computes Ext with complexes of smooth
projective modules; that comparison is a separate obligation.

## Sources and provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed p.309, Proposition 4.4 and
equation (4.4.1): "Ext^i denotes the i-th derived functor of Hom in the
category of smooth `O_m[GJ]`-modules". Proposition 4.10 on p.311 states
the same convention for its `l`-adic limit. Worker 13 read these
passages. Registered source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris's coefficient rings are `O_m = O/λ^m O` and `O`, where `O` is the
ring of integers of a `λ`-adic completion of the coefficient field (section
3, printed pp.307-308), and the group acting there is a locally profinite
`p`-adic group. These are specializations of the general scope here, which
is a domain of definition only. The source fixes no central character in Proposition 4.4; no
central-character variant is defined here. The derived-functor and
injective-resolution machinery is Mathlib's, at commit
`5ed2965256430c3649e86755f9576b54eca72435`. Harris's geometric input,
spectral sequence (4.4.1) and Hecke equivariance are separate obligations.
The imports were checked in Library commit
`f01c1864161b6d1cdc1d04b1f8d577dfd4e8400f`.
