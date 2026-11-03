# Invariant compact spatial maps for the separate smooth Godement complex

This module applies the existing invariants functor degreewise to the proper
compact spatial maps of the separate smooth Godement complex. It transports
the resulting chain maps to the already defined invariant compact complexes
and takes their module homology. Original-section formulas, naturality, and
identity and lax-composition laws are proved for these actual maps.

## Setting and the functor comparison

The commutative ring `R`, topological group `G`, spaces, and module carriers
share universe `u`. Each space has a `G`-action with continuous fixed
translations and `HasStableNeighbourhoods`. The map `f : C(X, Y)` is continuous,
equivariant by `hf`, and proper by `hp : IsProperMap f`. A second map
`g : C(Y, Z)` has corresponding witnesses `hg` and `hq`. Sheaves belong to the
existing category `SmoothTopologicalSheaf R G X` of smooth module sheaves on
the ordinary-open transport category.

Write `D_f` for `SmoothDirectImage.functor f hf`, `C_X` for
`smoothGodementCompactComplex R G X`, and `V_X` for
`smoothGodementInvariantCompactComplex R G X`. The functor

```text
I = SmoothGodementComparison.smoothInvariants R G
  = SmoothRep.toRep ⋙ Rep.invariantsFunctor R G
```

takes a smooth representation to its module of vectors fixed by every
element of `G`. Write `I_*` for its induced functor on cochain complexes
indexed by `ℕ`. The existing invariant compact-section functor is
definitionally compact sections followed by `I`.

`smoothGodementInvariantCompactComplexIso R G X` is the isomorphism

```text
α_X : C_X ⋙ I_* ≅ V_X.
```

It is constructed by whiskering
`Functor.mapHomologicalComplexCompIso` with
`Godement.smoothComplexFunctor R G X`. The input is the actual reflexive
isomorphism between the two presentations of the section functor. Thus the
comparison changes how the functors are composed, and its components act as
the identity on the underlying invariant compact sections.
`smoothGodementInvariantCompactComplex_map` proves that, for every original
sheaf morphism `a`,

```text
V_X.map(a) = I_*.map(C_X.map(a)).
```

Its proof is extensionality in the complex degree and the invariant section.

## Transported invariant compact chain maps

The remaining declarations are in the namespace
`Langlands.Cohomology.SmoothGodementCohomology.Spatial`. Let
`P_f(F) = compactMap f hf hp F` be the already constructed proper spatial
chain map in the category of smooth representations.
`invariantCompactNatTrans f hf hp` has type

```text
D_f ⋙ V_Y ⟶ V_X.
```

It is the composite of the inverse comparison on `Y`, degreewise invariants
of `compactNatTrans f hf hp`, and the comparison on `X`.
`invariantCompactMap f hf hp F` is its component. The theorem
`invariantCompactMap_eq` records the actual transport formula

```text
Q_f(F) = α_Y.inv(D_f(F)) ≫ I_*.map(P_f(F)) ≫ α_X.hom(F).
```

`invariantCompactMap_eq_map` proves that this is just
`I_*.map(P_f(F))` on the original presentations; its proof again uses
extensionality in each degree and section. In particular,
`invariantCompactMap_f` gives

```text
Q_f(F).f n = I.map(P_f(F).f n).
```

`invariantCompactMap_apply` states the formula on the original section of
an invariant compact section `s`: its image has original global section

```text
(((Godement.SmoothSpatial.complexMap f hf F).f n).hom.hom.app
  (Opposite.op ActionOpens.top)).hom (s.val.val)
```

with the smooth-direct-image subtype witness removed by `.val`.
The two projections `s.val.val` remove the invariant and compact-support
witnesses. Properness supplies the compact-support condition on the image.
Equivariance of the constructed compact chain map supplies its invariant
condition.

`invariantCompactMap_f_zero` specializes the degree formula to `I` applied
to the composite of compact sections of
`Godement.SmoothSpatial.zeroMap f hf F` and the existing proper
compact-section transformation at
`(Godement.smoothZeroFunctor R G X).obj F`. Thus the map in degree zero
uses the actual smooth Godement zero map.

## Naturality, identity and lax composition

`invariantCompactMap_naturality` retains every sheaf morphism `a : F ⟶ F'`:

```text
V_Y.map(D_f.map(a)) ≫ Q_f(F')
  = Q_f(F) ≫ V_X.map(a).
```

This is naturality of the constructed transformation. Let
`e : 𝟭 ≅ D_id` be `SmoothDirectImage.idIso` and
`c_fg : D_f ⋙ D_g ⟶ D_(g.comp f)` be
`SmoothDirectImage.compMap f hf g hg`. The equations are

```text
V_X.map(e.hom(F)) ≫ Q_id(F) = 𝟙,

V_Z.map(c_fg(F)) ≫ Q_(g.comp f)(F)
  = Q_g(D_f(F)) ≫ Q_f(F).
```

These are `invariantCompactMap_id` and `invariantCompactMap_comp`.
The proofs rewrite the maps as degreewise invariants of the actual compact
chain maps, use the existing compact identity or composition equation,
and apply functoriality of `I_*`. The lax comparison remains explicit;
its invertibility is not needed. These three laws also have reassociated
forms from their `reassoc` attributes.

## Module homology of the invariant complexes

`invariantCohomologyNatTrans f hf hp q` is the invariant chain
transformation whiskered by
`homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q`. Its type is

```text
D_f ⋙ smoothGodementInvariantCompactCohomology R G Y q
  ⟶ smoothGodementInvariantCompactCohomology R G X q.
```

`invariantCohomologyMap` is its component and
`invariantCohomologyMap_eq` identifies it with module homology of
`invariantCompactMap`. The theorems
`invariantCohomologyMap_naturality`, `invariantCohomologyMap_id` and
`invariantCohomologyMap_comp` prove the corresponding equations on these
existing cohomology objects. Naturality comes from the transformation;
identity and composition follow by applying the module homology functor
to the proved chain equations. All three have reassociated forms.

## Provenance and scope

This is an internal construction from `SmoothGodement.Spatial`,
`SmoothGodementCohomology`, `SmoothSheafCohomology`, and the invariants
functor of `SmoothGodementComparison.Invariants`, using Mathlib's functor
composition isomorphism for homological complexes. The comparison,
transport and homology maps are constructed from those actual functors
and maps. The section formulas and functoriality proofs above explain the
remaining intrinsic obligations. No external-source assertion is introduced.

The result is homology after taking degreewise invariants of compact
sections of the separate smooth Godement complex. No exactness of
invariants or commutation of invariants with homology is asserted. No
resolution exactness, acyclicity, right derived identification, comparison
with the full equivariant Godement route, compatibility with the existing
degree-zero cohomology isomorphisms, subgroup or quotient invariant spatial
maps, or analytic, etale or Shimura realization is proved here.
