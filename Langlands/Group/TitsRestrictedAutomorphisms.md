# Automorphisms permute the components of the restricted building

For a supplied abstract Tits system `h : IsTitsSystem B N π S`, this module
studies a group automorphism `φ : G ≃* G` with

```
hφ : ∀ P, IsAdmissibleParabolic B π S (P.map φ) ↔ IsAdmissibleParabolic B π S P,
```

that is, `φ` maps the facets of the restricted building (KP Remark 1.5.7)
bijectively to facets. It constructs a permutation `σ` of the irreducible
components of `S` and the induced vertex permutation of the polysimplicial
complex `restrictedComplex` of `TitsRestrictedPolysimplicial`. This vertex
permutation sends the product of component simplices of `P` to that of `φ(P)`,
and its coordinate `σ c` depends only on the coordinate `c`. This is the
statement needed to show that such automorphisms act by polysimplicial
automorphisms (KP Definition 1.5.1(13); compare the action of `G` in KP
Proposition 1.5.18(3)). It is an internal deduction from the existing
Tits-system API and the frozen `TitsSystemExchange` and
`TitsRestrictedPolysimplicial` candidates. No finiteness of `S` is required.

## Images of subgroups

`map_conjugateSubgroup` computes `φ(g L g⁻¹) = φ(g) φ(L) φ(g)⁻¹`.
`map_symm_map`, `map_map_symm` and `map_le_map_iff_equiv` record that
`φ` and `φ.symm` are inverse order isomorphisms on subgroups.

## Types

`standardParabolicSubgroup_self` proves `G_S = G`.
`isAdmissibleParabolic_conjugate_iff` proves that `g G_X g⁻¹` is admissible
exactly when `X` is admissible; the reverse direction uses uniqueness of
parabolic types. `isAdmissibleParabolic_borel` records that `B` is
admissible. `not_isAdmissibleType_componentSet` shows that no component type
`S_c` is admissible, and `exists_componentSet_subset_of_not_isAdmissibleType`
shows that every nonadmissible `Y ⊆ S` contains some `S_d`. Hence the
components are exactly the minimal nonadmissible types.

## The type correspondence

`TypeCorr φ a X Y` says that `X, Y ⊆ S` and `φ(G_X) = a G_Y a⁻¹`. Suppose
`ha : φ(B) = a B a⁻¹`.

* `exists_typeCorr_left`: every `X ⊆ S` corresponds to some `Y`. Indeed
  `a⁻¹ φ(G_X) a` contains `a⁻¹ φ(B) a = B`, so it is standard by the existing
  `exists_eq_standardParabolic`.
* `exists_typeCorr_right`: every `Y ⊆ S` corresponds to some `X`, by the same
  argument for `φ⁻¹(a G_Y a⁻¹) ⊇ φ⁻¹(a B a⁻¹) = B`.
* `typeCorr_subset_iff`: corresponding pairs satisfy `X ⊆ X' ↔ Y ⊆ Y'`,
  combining `standardParabolicSubgroup_le_iff` with the order isomorphisms
  given by `φ` and by conjugation. Uniqueness on both sides follows.
* `typeCorr_self`: `S` corresponds to `S`, since `φ(G) = G`.
* `typeCorr_isAdmissibleType_iff` (with `hφ`): corresponding types are
  admissible together.

`exists_typeCorr_componentSet` proves that every component type `S_c`
corresponds to a component type `S_d`. The type `Y` corresponding to `S_c` is
not admissible, so it contains some `S_d`. The type `Z` corresponding to
`S_d` is contained in `S_c` and is not admissible. It therefore contains some
component, which must be `S_c` itself. Thus `Z = S_c` and `Y = S_d`.

`exists_typeCorr_sdiff_singleton` proves that if `S_c` corresponds to `S_d`
and `s ∈ S_c`, then `S \ {s}` corresponds to `S \ {t}` for some `t ∈ S_d`.
The type `Y` of `S \ {s}` is not `S`, because `S` corresponds to `S`. Choose
`t ∈ S \ Y`. The type `Z` corresponding to `S \ {t}` contains `S \ {s}`. It
is not `S`, because `S \ {t}` is not `S`. Hence `Z = S \ {s}` and
`Y = S \ {t}`. Finally `S_c` is not contained in `S \ {s}`, so `S_d` is not
contained in `S \ {t}`, which forces `t ∈ S_d`.

## The component permutation

`exists_map_borel_eq` proves `φ(B) = a B a⁻¹` for some `a`. Since `φ(B)` is
admissible, it contains a conjugate `g B g⁻¹`. The subgroup `φ⁻¹(g B g⁻¹)` is
admissible and contained in `B`, so the existing
`eq_conjugate_borel_of_isAdmissible_of_le` makes it equal to `B`.
`symm_isAdmissibleParabolic_iff` transfers `hφ` to `φ⁻¹`.

`exists_component_map` maps the vertex `g G_{S \ {s}} g⁻¹` (`s ∈ S_c`) to
`φ(g) a G_{S \ {t}} (φ(g) a)⁻¹`. This is a vertex of the component `σ(c)`
chosen by `exists_typeCorr_componentSet`. `eq_of_isComponentVertex` shows that
a vertex has a unique component, because parabolic types are unique.
`exists_componentPerm` applies the construction to `φ` and `φ⁻¹`. Comparing
the components of one vertex and of its image shows that the two component
maps are inverse. It returns `σ : Equiv.Perm (Component S)` with
`IsComponentVertex (σ c) (φ Q) ↔ IsComponentVertex c Q`.

## The vertex permutation

For such `σ` (hypothesis `hσ`), `componentVertexMapEquiv hσ c` is `φ` as a
bijection from the vertices of `c` to those of `σ c`. Its inverse is `φ⁻¹`.
`autVertexEquiv hσ` is Mathlib's `Equiv.piCongr σ` of these bijections, so
`autVertexEquiv_apply` gives the coordinate formula
`(autVertexEquiv x) (σ c) = φ(x c)`. `respectsCoordinateFibers_autVertexEquiv`
deduces the existing `RespectsCoordinateFibers σ` condition.

`autVertexEquiv_mem_restrictedBox_iff` proves that `autVertexEquiv x` lies in
`restrictedBox (φ P)` exactly when `x` lies in `restrictedBox P`, for every
subgroup `P`. Coordinatewise this is `φ(P) ≤ φ(x c) ↔ P ≤ x c`, reindexed by
`σ`. Hence `restrictedBox_map` proves
`restrictedBox (φ P) = autVertexEquiv '' restrictedBox P`.

## Scope

These are results about an arbitrary supplied Tits system and an automorphism
of its group that preserves admissible parabolic subgroups. They do not show
that any particular group action has this property. They do not construct a
realization of a valuation quotient or prove any witness of
`RootValuationBuildingConstructionStatement`.
