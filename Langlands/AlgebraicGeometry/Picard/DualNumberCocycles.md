# Additive cocycles and actual dual-number unit cocycles

Let `k : Type u` be an arbitrary field, let `X : Scheme.{u}`, and let
`f : X ⟶ Spec k`. This module uses the actual scheme pullback and zero section
from `DualNumberThickening` and the proved actual unit kernel from
`DualNumberActualUnits`. All indexing types also lie in `Type u`.

For a family of opens `T : ι → X.Opens` and sections
`z i j : Γ(X, T i ⊓ T j)`, `unitCochain f T z` is the family of actual units
`1 + epsilon*z i j` on the pairwise intersections of `thickenedOpens f T`,
the inverse-image opens in the actual thickening.

The main assertions are:

- `isCocycle_unitCochain_iff`: the multiplicative cocycle condition for these
  actual units is equivalent to `CechDegreeOne.IsCocycle` for `z` in the
  actual structure module of `X`.
- `exists_isGauge_unitCochain_iff`: there is an arbitrary actual unit gauge
  from the cochain of `z` to the cochain of `w` exactly when `w - z` is an
  additive coboundary on `T`.
- `coboundaryIso`: an additive coboundary difference constructs an actual
  isomorphism of the modules obtained by `CocycleGluing.glued`.
- `nonempty_iso_unitCochain_iff`: when both `z` and `w` are additive cocycles,
  their actual glued modules are isomorphic exactly when `w - z` is an
  additive coboundary.

The coboundary convention is `d(b) i j = b j| - b i|`. The gauge convention
from `CocycleLineBundleGauge` is `h i j = a i| * g i j * (a j|)⁻¹`. Thus an
additive gauge coefficient `c` gives `w i j = c i| + z i j - c j|`, and the
corresponding coboundary is that of `-c`. The proof includes this sign.

No assertion above requires the family `T` to cover `X`. In that generality
`glued` denotes the specific sheaf of compatible components constructed in
`CocycleLineBundleProof`; the previously proved local-rank-one conclusion
applies on all of `X` when `T` is a cover. This module neither assumes nor
concludes that arbitrary-family glued modules are globally line bundles.

## Actual coefficient units and restriction

`coefficientUnit f U a` is the underlying actual unit of
`unitKernelEquiv f U (Multiplicative.ofAdd a)`. Its value is
`1 + projection.app U a * epsilonSection f U`. The module proves that this
map is injective, sends zero to one, sends addition to multiplication,
sends negation to inversion and sends subtraction to division. Its actual
zero-section reduction is one.

`coefficientUnit_restrict` and `coefficientUnit_restrict_val` give the
restriction formulas as units and underlying ring sections. They follow
from the proved actual kernel naturality. The inverse image of an
intersection is definitionally the intersection of the inverse images;
`unitCochain` uses that identification without choosing a new ring carrier.

For the forward direction of the cocycle equivalence, the multiplicative
cocycle identity is restricted to any inverse-image open inside a triple
overlap. Naturality of coefficient units and injectivity turn it into the
additive cocycle identity on the original open. Conversely, the additive
identity on the triple overlap implies the multiplicative identity by the
addition formula and actual restriction naturality.

## Coefficients of arbitrary units

A gauge between two normalized cocycles need not itself reduce to one.
The proof therefore constructs a coefficient homomorphism on all actual
units, rather than restricting the converse to normalized gauges.

`liftUnit f U` lifts units along the actual first projection, and
`unitReduction_liftUnit` proves that it splits actual reduction.
`normalizeUnit f U` sends a unit `a` to

```
a * (liftUnit f U (unitReduction f U a))⁻¹
```

in `UnitKernel f U`. The kernel membership uses the splitting identity;
commutativity gives the homomorphism law. `unitCoefficient f U` composes this
normalization with the inverse of `unitKernelEquiv`. It is a homomorphism
from all actual units to `Multiplicative Γ(X,U)`, and sends
`coefficientUnit f U a` to `Multiplicative.ofAdd a`.

The naturality lemmas for reduction, lifting, normalization and
`unitCoefficient` prove that this coefficient construction commutes with
actual restriction. For `unitCoefficient`, the proof applies the injective
kernel equivalence to the desired equality, then uses kernel naturality
and the established normalization naturality.

## Gauges, coboundaries and actual module isomorphisms

`coefficients_of_isGauge` starts with any actual unit gauge. The equivalent
multiplicative intertwining identity is an equality of units. Applying
`unitCoefficient`, its homomorphism law and its restriction naturality gives

```
w i j = coeff(a i)| + z i j - coeff(a j)|.
```

`isGauge_unitCochain_iff` proves that choosing coefficient units for the
gauge gives exactly this additive equation, with the chosen coefficients.
Its reverse direction applies `coefficientUnit` to the additive
intertwining identity and uses the actual restriction formula.

For `exists_isGauge_unitCochain_iff`, an arbitrary unit gauge supplies the
coboundary of the negatives of its coefficients. Conversely, a coboundary
of `b` gives the gauge of coefficient units with coefficients `-b`.
`coboundaryIso` chooses that gauge and invokes the actual `gaugeIso`.
Finally, `nonempty_iso_unitCochain_iff` combines the published classification
of all isomorphisms of `CocycleGluing.glued` with the cocycle equivalence and
the just-proved gauge/coboundary equivalence. This includes both directions
for arbitrary isomorphisms of these actual module sheaves.

## Provenance and limits

This is an internal construction from the published actual unit-kernel
comparison, the actual cocycle gluing and gauge classification, and the
existing definition of additive structure-module cocycles and coboundaries.
The normalization of arbitrary units is proved directly using the actual
projection splitting. The cocycle and coboundary results follow from
restriction naturality and the additive/multiplicative equivalence, and
are not assumed classification or cohomology inputs.

The module classifies isomorphisms between these explicit normalized-cocycle
constructions. It does not prove that every line bundle trivial on the zero
section has such a presentation, compare rigidifications, identify the
result with right-derived cohomology, or prove tangent linearity. Those
remain separate obligations of the host tangent-to-H1 proof.
