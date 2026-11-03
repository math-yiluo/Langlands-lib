# Spatial maps for the separate smooth Godement degree-zero functor

This module constructs a natural spatial map for the existing separate smooth
Godement degree-zero functor and proves its compatibility with coaugmentation,
identity, and the lax composition comparison for smooth direct image. All
constructions use the existing actual functors and maps; a spatial comparison
is not a field supplied by the caller.

## Scope and notation

The ring `R`, the group `G`, the spaces, and the module carriers share universe
`u`. The ring is commutative and `G` is a topological group. Each space has a
`G`-action with continuous fixed translations and `HasStableNeighbourhoods`.
A spatial map `f : C(X, Y)` is continuous and has the displayed equivariance
proof `hf`. A second such map `g : C(Y, Z)` has proof `hg`.

The sheaves are the existing module-valued sheaves on the ordinary-open
transport category, and the smooth category is its full subcategory of locally
smooth sheaves. These are the categories of `TopologicalSheaf` and
`SmoothTopologicalSheaf`, respectively.

For the formulas below, write:

- `I_X` for `smoothInclusion R G X`, `S_X` for `smoothCoreflector R`, and
  `ε` for the actual smooth-subsheaf inclusion `smoothSubsheafι R`;
- `Q_X` for `CoinducedFamilies.coinducedZeroFunctor`, which coinduces the
  ordinary underlying sheaf of stalk families;
- `C_X = I_X ⋙ Q_X ⋙ S_X` for its smooth coinduced model;
- `d_f` for `DirectImage.sheaf f hf (ModuleCat R)` and `D_f` for
  `SmoothDirectImage.functor f hf`;
- `i_f : D_f ⋙ I_Y ⟶ I_X ⋙ d_f` for the actual smooth-image inclusion;
- `q_f : d_f ⋙ Q_Y ⟶ Q_X ⋙ d_f` for
  `CoinducedFamilies.Spatial.coinducedSpatialNatTrans f hf`;
- `κ_f : d_f ⋙ S_Y ≅ S_X ⋙ D_f` for
  `SmoothDirectImage.coreflectorIso f hf`.

Functor composition `⋙` is written in Lean's application order. Thus
`C_X(F) = S_X(Q_X(I_X(F)))`. Composition `≫` is also in application order.
The namespaces of this module are under
`Langlands.Sheaf.Equivariant.Godement.SmoothSpatial`.

## Actual construction in the coinduced model

`underlyingMap f hf F` is the composite

```text
u_f(F) = Q_Y.map(i_f(F)) ≫ q_f(I_X(F)).
```

`coinducedNatTrans` constructs `D_f ⋙ C_Y ⟶ C_X ⋙ D_f` by whiskering
these inclusions and the existing coinduced spatial transformation with
smooth coreflection, then applying `κ_f.hom`.
`coinducedMap` is its component `A_f(F)`. The component formulas
`coinducedMap_eq` and `coinducedMap_eq_underlying` give

```text
A_f(F) = S_Y.map(u_f(F)) ≫ κ_f.hom(Q_X(I_X(F))).
```

The total inclusion formula `coinducedMap_inclusion` states

```text
I_Y.map(A_f(F)) ≫ i_f(C_X(F)) ≫ d_f.map(ε(Q_X(I_X(F))))
  = ε(Q_Y(I_Y(D_f(F)))) ≫ u_f(F).
```

Its proof unfolds the component and the actual section inclusions. The two
smoothness proofs are forgotten and the original section map remains.
`coinduced_hom_ext` proves that this total inclusion detects equality of maps
into `D_f(C_X(F))`: it uses equality of presheaf components, module maps and
sections, then extensionality for the two smooth-section subtypes.

`coaugmentation_coinducedMap` proves

```text
aC_Y(D_f(F)) ≫ A_f(F) = D_f.map(aC_X(F)),
```

where `aC` is `coinducedSmoothCoaugmentation`. After the two inclusions,
its proof uses the coaugmentation inclusion equation from `SmoothCoinduced`,
naturality of the actual coinduced coaugmentation along `i_f(F)`, the proved
coinduced spatial coaugmentation equation, and naturality of `i_f`.

## Identity and lax composition

Let `e : 𝟭 ≅ D_id` denote `SmoothDirectImage.idIso`, and let
`c_fg : D_f ⋙ D_g ⟶ D_(g.comp f)` denote
`SmoothDirectImage.compMap f hf g hg`. The equations proved here are

```text
C_X.map(e(F)) ≫ A_id(F) = e(C_X(F)),

Q_Z.map(I_Z.map(c_fg(F))) ≫ u_(g.comp f)(F)
  = u_g(D_f(F)) ≫ d_g.map(u_f(F)),

C_Z.map(c_fg(F)) ≫ A_(g.comp f)(F)
  = A_g(D_f(F)) ≫ D_g.map(A_f(F)) ≫ c_fg(C_X(F)).
```

These are `coinducedMap_id`, `underlyingMap_comp`, and
`coinducedMap_comp`. The identity proof combines the actual inclusion with
the smooth-direct-image unit, obtaining the identity before `Q_X`, and uses
`coinducedSpatialMap_id` and `coreflectorIso_id`. The underlying composition
proof uses naturality and composition of `q`, together with
`compMap_inclusion`. Applying smooth coreflection and using naturality and
the composition law of `κ` gives the final equation. In particular, the
composition comparison is used as a morphism; its invertibility is not an
assumption or conclusion.

## Transport to the separate smooth Godement functor

Write `H_X = smoothZeroFunctor R G X` and
`E_X : H_X ≅ C_X` for `smoothZeroCoinducedIso R G X`.
`zeroNatTrans` constructs `D_f ⋙ H_Y ⟶ H_X ⋙ D_f` by the actual composite

```text
t_f(F) = E_Y.hom(D_f(F)) ≫ A_f(F) ≫ D_f.map(E_X.inv(F)).
```

`zeroMap` is its component; `zeroMap_eq` records the formula and
`zeroMap_naturality` records naturality for every smooth sheaf morphism.
`zeroMap_comparison` states

```text
t_f(F) ≫ D_f.map(E_X.hom(F)) = E_Y.hom(D_f(F)) ≫ A_f(F).
```

The proof cancels the inverse and forward components through functoriality.
The proved coaugmentation comparison for `E` and the coinduced equation give
`coaugmentation_zeroMap`:

```text
smoothCoaugmentation_Y(D_f(F)) ≫ t_f(F)
  = D_f.map(smoothCoaugmentation_X(F)).
```

`zeroMap_id` and `zeroMap_comp` give the corresponding equations

```text
H_X.map(e(F)) ≫ t_id(F) = e(H_X(F)),

H_Z.map(c_fg(F)) ≫ t_(g.comp f)(F)
  = t_g(D_f(F)) ≫ D_g.map(t_f(F)) ≫ c_fg(H_X(F)).
```

Their proofs use naturality of `E` and the direct-image comparison, followed
by the coinduced laws. For composition, postcomposition with the isomorphism
`D_(g.comp f).map(E_X.hom(F))` detects equality. The laws with a `reassoc`
attribute also have reassociated forms.

## Provenance and remaining scope

This is an internal construction from the published `SmoothCoinduced`,
`CoinducedFamilies.Spatial`, and `SmoothDirectImageCoreflector` modules and
the functors they import. It extends their degree-zero maps by actual
whiskering, section inclusions, naturality and isomorphism transport. It
makes no additional claim about an external theorem.

The separate smooth Godement functor remains the one formed by forgetting
equivariance, applying the ordinary Godement functor and applying smooth
coinduction. This module supplies its spatial map. Higher complex maps,
exactness, acyclicity, derived comparisons, and analytic, etale or Shimura
specializations remain separate work. No preservation of smoothness by full
direct image is assumed.
