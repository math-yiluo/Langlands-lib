# Domain stalks of smooth schemes over arbitrary fields

This module proves the published Library proposition
`Langlands.AlgebraicGeometry.SmoothDomainStalks` with the exact interface

```lean
theorem Langlands.AlgebraicGeometry.smoothDomainStalks.{u} :
    Langlands.AlgebraicGeometry.SmoothDomainStalks.{u}
```

For every field `K : Type u`, scheme `X : Scheme.{u}`, and smooth morphism
`p : X ⟶ Spec (CommRingCat.of K)`, every structure-sheaf stalk of `X` is a
domain. Here `IsDomain` includes nontriviality and absence of zero divisors.
The universe `u` is arbitrary, and the closing theorem has no additional
outer assumptions.

## Affine chart and smooth section algebra

The private helper `smoothDomainStalks_of_domainLocalizations` reduces the
scheme assertion to the published ring proposition
`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations.{u, u}`.
Given a point `x`, `X.affineCover.exists_eq` supplies an affine chart `U`
and a point `y` mapping to `x`. The chart map is an open immersion, so its
composite `q` with `p` is smooth.

The ring map `q.appTop` goes from the global sections of the field spectrum
to `Γ(U, ⊤)`. Composing with the inverse of `Scheme.ΓSpecIso` gives a ring
map from `K` to `Γ(U, ⊤)`. The spectrum isomorphism induces a smooth ring
map, and `HasRingHomProperty.appTop` makes the second map smooth.
`RingHom.Smooth.comp` therefore makes their composite smooth. Installing
its algebra structure with `algebraize` and applying
`RingHom.smooth_algebraMap` makes `Γ(U, ⊤)` a smooth `K`-algebra.

## Prime localization and stalk transport

The affine chart point `y` corresponds to a prime ideal `P` of `Γ(U, ⊤)`.
The ring proposition gives `IsDomain (Localization.AtPrime P)`.
The stalk has its canonical section-ring algebra structure, supplied by
`TopCat.Presheaf.algebra_section_stalk`. The result
`IsAffineOpen.isLocalization_stalk` identifies it as a localization at
`P.primeCompl`. The canonical `IsLocalization.algEquiv` between these two
localizations transfers `IsDomain` to `U.presheaf.stalk y`.

The affine-cover map induces an isomorphism from the original scheme's
stalk at the image of `y` to the chart stalk at `y`. Transport through this
ring isomorphism gives `IsDomain (X.presheaf.stalk x)`.

The closing theorem supplies the imported published theorem
`Langlands.CommutativeAlgebra.smoothAlgebraDomainLocalizations.{u, u}`
to the private helper. Thus the ring assertion is discharged by a proof;
it is not an outer hypothesis of `smoothDomainStalks`.

## Provenance and contributions

This is an internal affine-chart derivation from the published algebra
theorem and the named Mathlib localization and stalk isomorphisms. The
statement's paired Markdown records its original Stacks Project derivation
through regularity and normality. The implemented proof uses the algebraic
localization theorem and the chart argument described here.

The construction of the smooth section algebra follows the affine setup
in the published `SmoothReducedProof`: Worker 129 authored that Lean
proof, and Worker 428 prepared its documentation. Worker 669 adapted the
chart argument to domain localizations, constructed the stalk transports,
and closed the present target. The imported algebra theorem is the separate
published proof by Worker 399.
