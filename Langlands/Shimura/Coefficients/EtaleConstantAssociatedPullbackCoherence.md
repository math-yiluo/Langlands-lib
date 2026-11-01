# Coherence of constant-module associated-sheaf base change

This is an internal derived construction. It reuses the actual comparisons in
[EtaleAssociatedPullbackCoherence](EtaleAssociatedPullbackCoherence.md),
[EtaleConstantAssociatedPullback](EtaleConstantAssociatedPullback.md),
[EtaleCrossCover](EtaleCrossCover.md), and the constant-sheaf identity and
composition laws in
[EtaleConstantPullback](../../Geometry/EtaleConstantPullback.md).
It asserts no additional result from Harris or Berkovich.

Let `f : Z ⟶ X` and `g : W ⟶ Z` be etale morphisms of actual schemes. Schemes,
the commutative coefficient ring `R`, the carriers of `ModuleCat R`, and the deck
group `G` share universe `u`. Write `r_f` for small-etale restriction, `C_X` for
the constant-sheaf functor lifted to `G`-actions, and `P_f` for actual geometric
pullback of cover actions. The cover `Y : Action X.Etale G` and representation
`M : Action (ModuleCat R) G` are arbitrary. No finiteness, torsor or
local-constancy hypothesis is required.

Write `A_X(Y,F)` for the associated invariant sheaf with sheaf-valued coefficient
action `F`, and `L_X(Y,M) = A_X(Y,C_X M)` for the constant-module version.
Let `α_f(M) : r_f(C_X M) ⟶ C_Z M` be the entire constant-action comparison and
`λ_f(Y,M) : r_f(L_X(Y,M)) ⟶ L_Z(P_f Y,M)` the constant-associated comparison.
In expressions involving coefficient actions, `r_f` means its lift by
`Functor.mapAction`.

`etaleConstantActionPullback_id` proves

```text
α_id(M) = coefficientRestrictionId(C_X M).
```

`etaleConstantActionPullback_comp` proves

```text
coefficientRestrictionComp(C_X M) ≫ α_(g ≫ f)(M)
  = r_g(α_f(M)) ≫ α_g(M).
```

Both equations are equalities of action morphisms, so they retain all group
operators. The proofs apply `Action.Hom.ext` and then the existing
`constantPullbackIso_id` and `constantPullbackIso_comp` equations on underlying
sheaf morphisms.

`etaleConstantAssociatedPullback_hom_app` exposes the defining factorization

```text
λ_f(Y,M) = associatedPullback_f(Y,C_X M) ≫ A_Z(P_f Y,-)(α_f(M)).
```

The new natural isomorphism `etaleConstantAssociatedPullbackComp` has type

```text
(L_X(Y,-) ⋙ r_f) ⋙ r_g ≅ L_W(P_(g ≫ f) Y,-).
```

It is constructed from the functor associator, restriction composition whiskered
by `L_X(Y,-)`, and the single-step constant-associated comparison.
`etaleConstantAssociatedPullbackComp_hom_app` identifies its hom component with

```text
restrictionComp(L_X(Y,M)) ≫ λ_(g ≫ f)(Y,M).
```

Let `p_Y : P_id Y ⟶ Y` be the actual first-projection identity-cover comparison,
and let `c_Y : P_(g ≫ f) Y ⟶ P_g(P_f Y)` be the actual single-to-iterated
fiber-product comparison. Cover change acts contravariantly on associated
sheaves. `etaleConstantAssociatedPullback_id` proves

```text
λ_id(Y,M)
  = restrictionId(L_X(Y,M)) ≫ etaleCrossCoverMap(id_G,p_Y,id_M).
```

The proof factors the constant comparison, uses the constant-action identity
law and the associated-sheaf identity law, and identifies the image of the
identity coefficient morphism with the identity on the constant action.

`etaleConstantAssociatedPullback_comp` proves

```text
restrictionComp(L_X(Y,M)) ≫ λ_(g ≫ f)(Y,M)
  = r_g(λ_f(Y,M)) ≫ λ_g(P_f Y,M)
      ≫ etaleCrossCoverMap(id_G,c_Y,id_M).
```

Its proof first establishes naturality of the cover change in the final
constant-action comparison. This local equation is proved by invariant-sheaf
`hom_ext`, the invariant inclusions and `coverPullback_natural`. Expanding the
defining factorization of `λ` then allows the associated-sheaf composition law
to apply. The local naturality equation moves the final constant-action
identification across cover change; functoriality and the constant-action
composition law combine the coefficient identifications. Naturality of the
second associated comparison completes the calculation. The geometric cover
map remains present in its contravariant direction throughout.

The laws are intrinsic to the actual comparisons: no desired coherence equation
or arbitrary comparison is an input. This unit does not implement coherence of
whole varying-group coefficient systems, inverse image along arbitrary
non-etale morphisms, algebraic-closure base change, compact supports, or a
particular Shimura tower realization. Those remain separate obligations of the
broader framework.
