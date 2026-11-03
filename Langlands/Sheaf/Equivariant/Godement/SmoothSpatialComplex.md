# Spatial maps of the separate smooth Godement complex

This module constructs the natural spatial chain map of the existing separate
smooth Godement complex from the actual degree-zero transformation in
`SmoothSpatialZero`. Every higher map is obtained by actual cokernel descent.
It proves augmentation, naturality, identity and lax-composition compatibility
for these chain maps.

## Setting and construction

The commutative coefficient ring `R`, topological group `G`, spaces `X`, `Y`,
`Z` and module carriers share universe `u`. Each space has a `G`-action with
continuous fixed translations and `HasStableNeighbourhoods`. The map
`f : C(X, Y)` is continuous and equivariant by `hf`; the second map
`g : C(Y, Z)` has the corresponding proof `hg`. The sheaves are the existing
smooth module-valued sheaves on the ordinary-open transport category.

Write `D_f` for `SmoothDirectImage.functor f hf`, `H_X` for
`smoothZeroFunctor R G X`, `η_X` for `smoothCoaugmentation R G X`, and
`K_X(F)` for `smoothComplex R G X F`. This is the separate smooth Godement
complex formed by iterating actual cokernels in the smooth sheaf category
starting with `H_X` and `η_X`. In particular, it retains smooth coinduction
in degree zero.

`SmoothSpatial.zeroNatTrans f hf` is the actual transformation
`D_f ⋙ H_Y ⟶ H_X ⋙ D_f`. Its component is denoted `t_f(F)` below. Its
proved coaugmentation square is `coaugmentation_zeroMap`. The functor
`D_f` is additive, hence preserves zero morphisms; no preservation of
cokernels by `D_f` is needed.

In `Langlands.Sheaf.Equivariant.Godement.SmoothSpatial`, `complexMap f hf F`
constructs the genuine chain map

```text
L_f(F) : K_Y(D_f(F)) ⟶ D_f,complex(K_X(F)),
```

where `D_f,complex` is Mathlib's degreewise
`D_f.mapHomologicalComplex (ComplexShape.up ℕ)`. The definition specializes
`CokernelComplex.Lax.complexMap` to the actual degree-zero transformation
and its proved coaugmentation compatibility.

The generic construction starts the residual comparison at the identity.
At each successor it forms the term map, composes with the target quotient,
and descends through the source cokernel. The coaugmentation square makes
that composite vanish on the source coaugmentation. The defining quotient
equations prove compatibility with the differentials. Thus all higher
components and their chain-map equations are constructed, not inputs.

`complexNatTrans` packages these maps as

```text
D_f ⋙ smoothComplexFunctor R G Y
  ⟶ smoothComplexFunctor R G X ⋙ D_f,complex.
```

`complexNatTrans_app` identifies its components with `complexMap`.
`complexMap_f` identifies degree `n` with the constructed `Lax.termMap` at
that degree. `complexMap_f_zero` states `L_f(F).f 0 = t_f(F)`.
`augmentation_complexMap` gives

```text
smoothAugmentation_Y(D_f(F)) ≫ L_f(F).f 0
  = D_f.map(smoothAugmentation_X(F)).
```

`complexMap_naturality` states the square for every original smooth sheaf
morphism `a : F ⟶ F'`, with `K_Y.map(D_f.map(a))` on the source and
`D_f,complex.map(K_X.map(a))` on the target. These results specialize the
proved generic component, augmentation and naturality equations.

## Identity and lax composition

Let `e : 𝟭 ≅ D_id` be `SmoothDirectImage.idIso`. Its forward component is
the actual smooth-direct-image unit. `complexMap_id` proves

```text
K_X.map(e.hom(F)) ≫ L_id(F) = e.hom_complex(K_X(F)),
```

where the right side is the chain map obtained by applying
`NatTrans.mapHomologicalComplex` to `e.hom`. This formula uses the actual
identity comparison rather than requiring `D_id` to be definitionally the
identity functor.

Let `c_fg : D_f ⋙ D_g ⟶ D_(g.comp f)` be
`SmoothDirectImage.compMap f hf g hg`. `complexMap_comp` proves

```text
K_Z.map(c_fg(F)) ≫ L_(g.comp f)(F)
  = L_g(D_f(F)) ≫ D_g,complex.map(L_f(F)) ≫ c_fg,complex(K_X(F)).
```

Here `c_fg,complex` is the degreewise natural transformation obtained from
`c_fg`. Neither this comparison nor the spatial chain maps are assumed or
proved to be isomorphisms.

Both laws use `CokernelComplex.Lax.complexMap_transformation` from
`LaxNaturality`. For identity, the functor transformation is `e.hom` from
the identity functor to `D_id`; its degree-zero square is `zeroMap_id`.
The strict generic identity chain map then reduces to the identity. For
composition, the functor transformation is `c_fg`; its degree-zero square
is `zeroMap_comp`. The generic square is combined with the already proved
strict-composite law `Lax.complexMap_comp`. This proves all higher laws
from the actual degree-zero laws and uniqueness of cokernel descent.
The augmentation, naturality, identity and composition equations also have
reassociated forms through their `reassoc` attributes.

## Provenance and remaining scope

The construction is internal to the published separate smooth Godement and
iterated-cokernel framework. It imports `SmoothSpatialZero` and the generic
`CokernelComplex.LaxNaturality`, retaining their actual maps and proved
compatibility laws. It makes no additional external-source assertion.

It supplies chain maps of the separate smooth Godement complex of smooth
sheaves. It does not identify this with smooth sections of the full
equivariant Godement complex. Compact-support maps, cohomology maps,
exactness, acyclicity, derived identifications and analytic, etale or
Shimura specializations remain separate. No full-image preservation of
smoothness and no right exactness of smooth direct image is assumed.
