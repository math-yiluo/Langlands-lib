# Harris coefficients on geometrically pulled-back torsors

This module specializes the constructed
[whole varying-torsor comparison](EtaleVaryingSystemPullback.md) to the
[full Harris coefficient system](HarrisEtaleCoefficients.md). It identifies
restricted sheaves with the sheaves associated independently to actual scheme
fiber products. It then gives ordinary section and cohomology pullbacks with
that associated system as target.

## Inputs and scope

The inputs are the existing finite-dimensional algebraic representation `ρ`,
its number field `L`, every coefficient place over the rational finite place
`p`, a compact open level `U`, and a natural-number reduction scalar `m`.
Write `R = HarrisCoefficientIntegers L p` and
`I = harrisCoefficientScalarIdeal L p m = Ideal.span {(m : R)}`.
At index `op n`, `harrisCoefficientDiagram ρ p U m` has coefficient
`Λ / I^n Λ` for the full stable lattice `Λ`. The scalar `m` is distinct
from the exponent `n`: every `n`, including zero, is retained. No
trivial-representation or selected-coefficient-place specialization is made.

The scheme `X`, compatible diagram `Y` of small-etale covers with the Harris
congruence groups, and proofs `hY` that every cover is a finite geometric torsor
are supplied. The new base is an actual scheme `Z` with an **etale** morphism
`f : Z ⟶ X`. Algebra, number field, representation, schemes, deck-group
carriers and coefficient modules use universe `u`.

Write `Yf = (etaleTorsorDiagramPullback f _).obj Y`. Its underlying schemes are
the actual fiber products of the covers with `Z` over `X`; its actions and
transitions are geometrically pulled back. The proof
`etaleTorsorDiagramPullback_isFiniteGeometricTorsor` supplies every target
torsor proof `hYf`. No target coefficient sheaf, comparison, or commutative
square is assumed as input.

## Whole coefficient comparison

`harrisEtaleCoefficientSystemPullback` constructs the isomorphism

```text
harrisEtaleRestrictedCoefficientSystem(X,Y,hY,f)
  ≅ harrisEtaleCoefficientSystem(Z,Yf,hYf).
```

It evaluates `etaleAssociatedVaryingSystemPullback` at the actual full
`harrisCoefficientDiagram`. The generic theorem has already proved compatibility
with the coefficient-reduction leg followed by the inverse finite-torsor
cover-comparison leg. Thus this is an isomorphism of complete diagrams, retaining
all transitions, rather than an unrelated family of pointwise isomorphisms.

The `hom_app` and `inv_app` equations identify its components with the forward
and inverse `etaleConstantAssociatedPullback` components at the same Harris
representation. `harrisEtaleCoefficientSystemPullback_naturality` records its
square with every original and pulled-back coefficient transition.

## Sections and ordinary cohomology

`harrisEtaleTorsorSectionsIso` and `harrisEtaleTorsorCohomologyIso q` postcompose
the coefficient isomorphism with actual global sections and ordinary small-etale
cohomology on `Z`. Their source is the corresponding restricted system from
[HarrisEtaleDerivedPullback](HarrisEtaleDerivedPullback.md); their target is the
existing construction applied independently to `Z,Yf,hYf`.

`harrisEtaleTorsorSectionsPullback` and
`harrisEtaleTorsorCohomologyPullback q` compose the previously constructed
geometric section/cohomology maps with these identifications. The `app`
equations show that each component first uses actual geometric pullback, then
applies the target section/cohomology functor to the canonical associated-sheaf
comparison. The cohomology naturality theorem expresses compatibility with
every transition of both actual Harris systems.

The coefficient, section and cohomology comparisons are isomorphisms between
two target descriptions. The geometric maps from `X` to `Z` are morphisms;
this module makes no claim that those pullback maps are isomorphisms.

## Provenance and remaining obligations

This is an internal specialization and composition of constructed project
functors, with no new literature theorem asserted. Naturality of the generic
whole-system comparison proves the coefficient square; functoriality transports
it to sections and cohomology. Composition of natural transformations gives the
actual new pullback maps and their transition compatibility.

The genuine input torsors have not been constructed here from particular
Shimura varieties. This module treats one etale base change. Iterated
associated-sheaf comparison coherence, arbitrary non-etale inverse image,
algebraic-closure base change, derived recovery for these new target maps,
compact support, smooth or Galois actions, and infinite coefficient or level
limits remain separate constructions or theorem obligations.
