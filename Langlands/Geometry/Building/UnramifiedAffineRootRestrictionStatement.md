# Unramified descent of affine roots

`Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement` is an
unproved Prop-valued statement, universe polymorphic in `u`. It says that, along a
Galois-fixed lift of the lower apartment into the upper one, the relative affine roots
are exactly the nonconstant restrictions of the absolute affine roots. The module only
states this; it proves nothing.

## Source and provenance

The statement is an internal set-equality formulation of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition 9.4.28, printed pages 359–360 (PDF
pages 390–391). Its setting is KP 9.4.27 (printed page 359, PDF page 390). Remark
9.4.26 (printed pages 358–359, PDF pages 389–390) gives the linear analogue. It is not a verbatim numbered
statement of the book. The authors' corrections of 1 November 2024 do not amend
9.4.23, 9.4.26, 9.4.27 or 9.4.28. Their only change in Section 9.4 removes the
non-divisibility restriction from Proposition 9.4.8.

In KP's notation, `T ⊃ S` is a special `k`-torus and `A` is the corresponding special
`k`-apartment of `B(G_K)`, so that `A^Γ` is the apartment of `S`. `Ψ(T, G)` is the
absolute affine root system and `Ψ(S, G)` the relative one. Proposition 9.4.28 asserts
two things:

1. For every relative affine root `ψ` with derivative `a`, and every `b ∈ Φ(T, G)`
   restricting to `a`, there is an absolute affine root `ψ_b` with derivative `b` whose
   restriction to `A^Γ` is `ψ`.
2. Conversely, if the restriction to `A^Γ` of an absolute affine root is not constant,
   then that restriction is a relative affine root.

The Lean statement asserts the set equality

```
restrictedRoots a D.affineRoots = DS.affineRoots,
```

where `AffineRootSystem.restrictedRoots a Ψ` is the set of composites `ψ.comp a`, for
`ψ ∈ Ψ`, whose linear part is nonzero. Inclusion `⊆` is part (2). Inclusion `⊇` is the
existence part of (1): every relative affine root is the restriction of some absolute
affine root. The Lean statement does not assert the refinement that `ψ_b` exists for
*every* root `b` restricting to `a`. So it claims no more than Proposition 9.4.28. Part (1)
gives `⊇` because every relative root is the restriction of some root of `(T_K, G_K)`
(Remark 9.4.26).

KP prove 9.4.28 with Proposition 9.4.23 (printed page 357, PDF page 388), applied
to the parahoric group schemes of `(G, S)` and of `(G_K, T_K)` at a point where the
affine root vanishes. 9.4.23 identifies the roots of the reductive quotient of the special
fiber with the derivatives of the affine roots that vanish at the point. That input is not
in the Library. This is why the step is stated here as a separate proposition.

## Binders

The binders up to `C`, the V 6 hypothesis and the lets `fixed` and `φ` are copied verbatim
from `Langlands.Geometry.Building.UnramifiedSpecialPointDescentStatement`. They are:

- `F : Type u`, any nonarchimedean local field (`Field`, `ValuativeRel`, `TopologicalSpace`,
  `IsNonarchimedeanLocalField`), in equal or mixed characteristic. `K` is the Library's
  maximal unramified extension `inertiaFixedField F`. `Aut(K/F)` is
  `inertiaFixedField F ≃ₐ[F] inertiaFixedField F`. Scalar extension is base change along
  `algebraBaseMap F K`.
- `G` over `Spec F` with `hG : IsConnectedReductive G`. The affine and smooth instances
  come from `hG`. A maximal split torus `iS : S.toGrp ⟶ G` is given with `hiS`.
- An `F`-torus `T` with `iT : T.toGrp ⟶ G`, and `f : S ⟶ T` with
  `CommGroupScheme.groupHom f ≫ iT = iS`.
- `hiT`: `T_K` is a maximal split torus of `G_K`, so `T` is a special torus in KP's sense.
  The monomorphism instances come from `hiS` and `hiT` via `mono_of_isMaximalSplitTorus`.
- `hE : RelativeRoot.HasOppositeFactorPairs` for `(G_K, T_K)`. This is the existing
  hypothesis needed to form `torusFieldRestrictedRootFunctionFamily`.
- `D : KPApartmentData` for `(G_K, T_K)`, normalized by the order of
  `MaximalUnramified.valuation F`. This is an equipollence class of valuations of the root
  datum, and its apartment plays the role of KP's `A`. Also `C : CentralizerDatum` for
  `(G_K, T_K)`, with `IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C`
  (V 6).
- `fixed x`: the point `x : D.Apartment` is fixed by the coefficient action
  `RootFunctionFamily.galoisAction` of every `σ ∈ Aut(K/F)`.
- `φ x : RootFunctionFamily S G`: the existing torus-then-field restriction
  `torusFieldRestrictedRootFunctionFamily` of the valuation `x`, from `T_K` over `K` to `S`
  over `F`.
- `DS : KPApartmentData iS (localFieldOrder F)`, whose carrier is exactly
  `{φ x | fixed x}`. Its apartment plays the role of KP's `A^Γ`. This carrier hypothesis is
  the one of `UnramifiedSpecialPointDescentStatement`.

The statement keeps `C`, V 6 and the carrier hypothesis so that its setting is the same
as that of the published special-point statement.

## The affine map

The statement quantifies over every affine map `a : DS.Apartment →ᵃ[ℝ] D.Apartment` with
three properties. These properties make `a` play the role of KP's inclusion
`A^Γ ⊂ A`.

- `∀ w, fixed (a w)`: the image consists of `Aut(K/F)`-fixed points.
- `∀ w, w.val = φ (a w)`: each point `w` is the field restriction of its image.
- `a.linear.comp (rootAnnihilator iS).mkQ = torusFieldTranslationMap F K f iT hiS.isSplitSubtorus.1`.
  Here `torusFieldTranslationMap` (from
  `Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement`) is
  `descentCocharacterMap F K f` followed by the quotient map onto the reduced
  translation space of `(G_K, T_K)`. So the linear part of `a`, pulled back to the real
  cocharacter space `V(S)`, is induced by the push-forward of real cocharacters
  `V(S) → V(T_K)`.

The third property is what makes the derivatives of `ψ.comp a` the restrictions of
derivatives. If `ψ` has derivative `rootForm b` for a root `b` of `(G_K, T_K)`, then the
linear part of `ψ.comp a` is `ψ.linear ∘ a.linear`. Pulled back to `V(S)`, this is
`rootForm b ∘ (quotient map) ∘ descentCocharacterMap`, which is the pairing with the
restriction of `b` to `S`. In particular, `ψ.comp a` is constant exactly when `b` restricts
to zero on `S`. This matches KP's distinction between constant and nonconstant
restrictions.

The statement does not assume that `a` is injective, surjective onto the fixed points, or
given by a particular construction.

## Conclusion and use

The conclusion is `AffineRootSystem.restrictedRoots a D.affineRoots = DS.affineRoots`.
`KPApartmentData.affineRoots` is the set `Ψ` of KP Definition 6.3.4, for `D` over `K` and
for `DS` over `F`.

`Langlands.Geometry.Building.AffineRootRestriction` contains two lemmas that use such an
equality. `AffineRootSystem.facet_restrictedRoots_eq_preimage` turns it into "facets of
`DS` are preimages under `a` of facets of `D`". `AffineRootSystem.isSpecialPoint_of_restrictedRoots_eq`
turns it into "a point whose image is special for `D.affineRoots` is special for
`DS.affineRoots`". These are the facet and special-point clauses of apartment-compatible
descent (KP Corollary 9.4.31 and Proposition 9.9.2).

This statement was written for Task 6314. Its intended application is the affine map
`descentAffineMap`, built from `descentPoint` in Worker 192's pending candidate module
`Langlands.Geometry.Building.UnramifiedDescentAffineApartment`. That map satisfies the
three properties:

- the fixed-image property by `descentAffineMap_fixed`;
- the lifting property by `descentPoint_val`;
- the linear-part property definitionally, because its linear part is a `Submodule.liftQ`
  of the same composite.

A private compile check confirmed that the statement then yields that module's
root-restriction premise.
