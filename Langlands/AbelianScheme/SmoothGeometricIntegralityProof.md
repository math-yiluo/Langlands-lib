# Geometric integrality of smooth geometrically connected schemes over fields

The theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality.{u}` proves exactly the
published proposition
`Langlands.AbelianScheme.SmoothGeometricIntegrality.{u}`. The statement module
is imported unchanged. For every field `K : Type u`, scheme
`X : Scheme.{u}`, and morphism `p : X ⟶ Spec (CommRingCat.of K)`, it proves

```text
Smooth p → GeometricallyConnected p → GeometricallyIntegral p.
```

The universe `u` is arbitrary. The theorem has no additional outer
hypotheses, and all three morphism predicates are Mathlib's predicates.

## Implemented proof

The proof installs the given smoothness and geometric connectedness as
local instances and constructs `GeometricallyIntegral p`. Its field
`geometrically_isIntegral` asks for integrality on every field-valued
pullback square. Thus fix any field `L : Type u`, any morphism
`y : Spec L ⟶ Spec K`, and any pullback square with source `Z` and
projections `fst : Z ⟶ X` and `snd : Z ⟶ Spec L`.

`MorphismProperty.of_isPullback h hp` transfers smoothness of `p` to
`snd`. A smooth morphism is locally of finite type, and the spectrum of a
field is locally Noetherian. Hence
`LocallyOfFiniteType.isLocallyNoetherian snd` gives local Noetherianity of
`Z`.

`GeometricallyConnected.geometrically_connectedSpace y fst snd h`
supplies `ConnectedSpace Z` on this same pullback. This includes
nonemptiness. The published theorem
`Langlands.AlgebraicGeometry.smoothDomainStalks`, applied to `L`, `Z`,
and `snd`, supplies a domain at every structure-sheaf stalk of `Z`.
Here `IsDomain` includes nontriviality and absence of zero divisors.

The published theorem
`Langlands.AlgebraicGeometry.connectedLocallyNoetherianDomainStalksIntegral`
combines these three facts to give `IsIntegral Z`. Its proof constructs
irreducible open neighborhoods using finite generation of localization
kernels, makes irreducible components open, and uses connectedness for
irreducibility; domain stalks give reducedness. Applying this theorem
discharges the arbitrary pullback obligation and therefore proves
`GeometricallyIntegral p`.

This tests every field-valued base change in Mathlib's definition, rather
than only one chosen algebraic closure. No global quasi-compactness,
perfectness, characteristic, separation, properness, group structure,
normality, regularity, reducedness, irreducibility, or prior integrality
hypothesis is added.

## Provenance and contributions

This is an internal assembly of the two published scheme theorems and
Mathlib's base-change and local Noetherianity results. The unchanged
statement's paired Markdown records the original Stacks Project
derivation through regularity, normality, and open irreducible
components. The implemented proof uses the published domain-stalk
criteria instead. In particular, the connected-domain-stalk theorem's
weaker hypothesis is justified by its own local algebra proof; it is
not attributed verbatim to a Stacks result about normal schemes.

Worker 416 wrote this assembly and its documentation. The imported
smooth-domain-stalk proof is by Worker 669, with contributions by
Workers 129 and 428; the connected-domain-stalk proof is by Worker 447,
with interface and component-reduction contributions by Worker 416.
Their paired documentation explains the respective proofs. All
prerequisites are published, and no rigidity theorem enters this proof.
