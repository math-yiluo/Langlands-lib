# Point comparison of actual finite Harris orbit covers

This internal construction compares the actual finite-etale orbit covers
chosen by `harrisIntegralCMFiniteOrbitCover` at two geometric points. It
constructs an isomorphism over the original test scheme, proves its actual
fibre and distinguished-point formulas, and proves its compatibility with
every original Harris level transporter. It retains a supplied fibre-functor
path and a source reference level; it does not construct representing PEL
geometry.

## Actual inputs and conventions

The universe-zero arithmetic data are `D`, its Harris signature charts `C`,
and the prerequisite package `P`, with the same field, quadratic-extension,
algebra and scalar-tower instances as the imported Harris construction. Over
`S` one supplies an abelian scheme `B`, its dual witness `W`, and a morphism
`lam : B ⟶ W.dual P`. The test `T : Over S` is quasi-separated, connected
and locally noetherian. The integral action is the original ring homomorphism
from `D.harrisHodgePELIntegralOrder C` into the endomorphisms of the actual
base change of `B` to `T`. No full CM condition or polarization proof for
`lam` is required by this conditional comparison.

The finite Weil transition and rational profinite-integer/adele comparison
prerequisites, torsion finite-etaleness, invertibility of every indexed
torsion order on `T.left`, and finiteness and etaleness of the corresponding
roots-of-unity schemes remain explicit. The points
`s : Spec Ω ⟶ T.left` and `r : Spec Ω' ⟶ T.left` may have different
algebraically closed fields. Both actual fibre finiteness witnesses `hs`
and `hr` and a path

```text
path : fiberFunctor s hs ≅ fiberFunctor r hr
```

are supplied. The construction uses the published geometric continuous-action
equivalence, with its actual connectedness, local Noetherianity and
algebraic-closure hypotheses.

Write `H` for the original scalar-extension similitude group, `Raw_s(V)`
for the right quotient of actual Weil frames at `s` by the subgroup of
`(hodgeLevelFunctor D C).obj V`, and `Γ_s` for `FundamentalGroup s hs`.
The right action is precomposition, expressed as a left action of the
opposite group, and the commuting left action is actual Tate monodromy.
The analogous notation at `r` uses exactly the corresponding original
actions. Write `R_V` for `harrisIntegralCMWeilRawPointEquiv ... path` at
that subgroup. It is the published raw equivalence induced by actual
Weil-frame transport.

## Reference levels and actual fibre equivalence

For original Harris levels `U,V`, the input

```text
hU : Nonempty ((harrisIntegralCMFullActionLevelTower ... s hs ...).obj U)
```

is a reference fixed level at the source point. It is the same premise used
by the existing finite orbit-cover construction to prove orbit finiteness
and continuity. `harrisIntegralCMFullActionLevelPointNonempty` maps this
witness through the hom component of the original full-level point
isomorphism to obtain the target reference level. Target nonemptiness is
therefore a conclusion, not an additional input.

For any raw class `q : Raw_s(V)`, the already proved orbit-membership
preservation and reflection restrict `R_V` to an equivalence

```text
Γ_s · q ≃ Γ_r · R_V(q).
```

The private `rawOrbitPointEquiv` is exactly this subtype restriction.
Compose it with the source actual cover-fibre equivalence and the inverse
target cover-fibre equivalence. The resulting public definition
`harrisIntegralCMFiniteOrbitCoverPointFiberEquiv` is an equivalence

```text
e : Fiber s (C_s(U,V,hU,q)) ≃
      Fiber r (C_r(U,V,targetNonempty,R_V(q))).
```

Here `C_s` and `C_r` denote the original chosen finite-etale covers.
The theorem with suffix `_val` proves that applying the target fibre
comparison to `e(x)` gives the raw value `R_V(fibre_s(x))`.
The theorem with suffix `_smul` proves

```text
e(g • x) = pathConjugation path g • e(x).
```

Its proof uses the two original cover-fibre monodromy formulas and the
published actual raw path-transport monodromy identity. It does not accept
an equivariance or comparison square as an input.

## Lifting to the actual cover isomorphism

The private lifting helper first turns a path-equivariant fibre equivalence
`e : Fiber s Y ≃ Fiber r Z` into a `Γ_s`-equivariant equivalence by composing
with the inverse of the component `path.app Z`. The path component itself
intertwines the two actual evaluation actions: this follows directly from
path conjugation and the inverse identity of the natural isomorphism.
`Action.mkIso` packages the resulting equivalence, and `ObjectProperty.isoMk`
retains the continuous-action category's object property. Full faithfulness
of `continuousActionFunctor s hs`, obtained from the published
`geometricContinuousActionEquivalence`, lifts it with `preimageIso` to
`Y ≅ Z`. The private fibre formula follows from `map_preimage`.

Applying that construction to the preceding actual Harris equivalence gives
`harrisIntegralCMFiniteOrbitCoverPointIso`:

```text
I_V(q) : C_s(U,V,hU,q) ≅ C_r(U,V,targetNonempty,R_V(q)).
```

This is an isomorphism in `Cover T.left`; in particular its underlying
scheme morphisms are over the unchanged actual test scheme. The theorem
`harrisIntegralCMFiniteOrbitCoverPointIso_fiber` proves, for every actual
source lift `x`,

```text
path_Z(x ≫ I_V(q).hom) = e(x).
```

The suffix `_raw` combines this equation with `_val` to prove that the raw
evaluation of its left side is `R_V(fibre_s(x))`. The suffix `_point` applies
the target fibre equivalence's injectivity and the original distinguished
raw-class identities to prove

```text
path_Z(point_s(q) ≫ I_V(q).hom) = point_r(R_V(q)).
```

The path component is necessary: the left source point is defined over
`Ω`, whereas the target distinguished lift is defined over `Ω'`.

## Original transporter square

For every original arrow `f : V ⟶ Z`, let `t_f` be its original raw right
translation, with the conjugation condition already carried by the mapped
Harris level arrow. Given raw classes `q,z` and the source equation
`t_f(q)=z`, the target equation `t_f(R_V(q))=R_Z(z)` is proved using the
published actual raw transport/translation formula. It is not a separate
assumption. The theorem
`harrisIntegralCMFiniteOrbitCoverPointIso_naturality` proves equality of
actual cover morphisms

```text
I_V(q).hom ≫ transport_r(f) = transport_s(f) ≫ I_Z(z).hom.
```

The proof checks actual source fibres, using faithfulness of the source
continuous-action functor. After applying the path component and the
injective target fibre comparison, naturality of that path component moves
it past the target transporter. The established `_raw` formulas and the
original cover transporter fibre formulas reduce the two sides to the
actual raw translation/point-transport identity. Thus the square is proved
for the existing cover morphisms, not for newly postulated transitions.

## Provenance and remaining obligations

All results are internal deductions from the published Harris raw transport,
selected-orbit, finite orbit-cover and cover-map modules and the actual
finite-etale continuous-action equivalence. The only generic helpers are
private implementation details. No literature assertion is introduced as
an axiom, and no new external source is cited.

The isomorphism is constructed for a supplied path. This file does not claim
path independence of these chosen scheme isomorphisms, construct paths,
or identify all dependent choices of covers. It does not prove
representability of the entire level set or the normalized rational-isogeny
moduli problem, establish its determinant/Lie or Rosati comparisons, or
construct an admissible smooth projective PEL representing scheme.
`DivisionCMRepresentabilityStatement` remains open.
