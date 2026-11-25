# Derivatives of affine roots over the maximal unramified field

`Langlands.Geometry.Building.unramifiedAffineRootDerivatives` proves the exact
Library proposition `UnramifiedAffineRootDerivativesStatement.{u}` at every
universe `u`. For every nonarchimedean local field `F`, every affine group scheme
`H` over `K = Langlands.LocalGalois.Separable.inertiaFixedField F`, and every
supplied `C : MaximalUnramified.BuildingData F H`, it establishes

```lean
AffineRootSystem.derivativeRoots C.affineRoots = Set.range (rootForm C.i)
```

These are the ordinary affine roots of the supplied apartment, and the equality
includes multipliable relative roots and their doubles.

## Implemented proof

The proof specializes the published theorem `quasiSplitDerivativeAffineRoots`
from `Langlands.Geometry.Building.QuasiSplitDerivativeAffineRootsProof`.
Its statement applies to a henselian field with a surjective integer-valued
valuation, a quasi-split affine group, a prescribed maximal split torus, and
arbitrary apartment and centralizer data satisfying full V 6 compatibility.

Take the field to be `K` and the valuation to be `MaximalUnramified.valuation F`.
The published results `MaximalUnramified.valuation_surjective F` and
`MaximalUnramified.valuationSubring_isHenselian F` provide surjectivity and
henselianity. The datum `C` supplies connected reductivity of `H`, so
`MaximalUnramified.isQuasiSplit F C.isConnectedReductive` provides the
quasi-splitness required by the general theorem.

The remaining arguments are precisely `C.S`, `C.i`, `C.isMaximalSplitTorus`,
`C.apartment`, `C.centralizer`, and `C.isOmegaCompatible`.
By definition, `MaximalUnramified.BuildingData F H` is
`IntegerValuationBuildingData (MaximalUnramified.valuation F) H`, and
`C.affineRoots` abbreviates `C.apartment.affineRoots`. The conclusion of the
general theorem is therefore definitionally the required equality for `C`.

All field, group and apartment premises of the general theorem are discharged
by these published results or by the supplied datum. The proof adds no
hypothesis to the target. In particular, it requires no topology or local-field
instance on `K`, no Axiom V 7, and no restriction excluding doubled roots.

## Provenance

This proof is an internal composition of published Library theorems. The target
statement's paired Markdown explains its relation to the derivative part
`∇Ψ = Φ` of Kaletha–Prasad Proposition 6.3.13, including the distinction between
the supplied V 0–V 6 data and the source's V 7 argument. The general quasi-split
theorem used here takes a different route: it constructs an apartment with
algebraically bounded root filtrations and uses uniqueness of full-V 6 classes
to identify it with the supplied apartment. Its bounded-filtration argument
handles multipliable roots through the actual quotient by the doubled-root
group. This module uses that published theorem directly.
