# Order-linear compatible families under coefficient extension

For an actual formal O-module atlas X with a full order action E, this module
upgrades the full compatible-family comparison of `AtlasBaseChangePoints` to
a D-linear equivalence. It constructs a natural isomorphism of the actual
order-module point functors, restricts it to nilpotent coefficient tests, and
specializes these constructions to special formal division-order atlases.

## Source and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), permits formal groups glued over localizations in the paragraph
before section 2. Section 2 A defines special formal O_D-modules using an action
extending O and the geometric tangent characters. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This module gives a derived comparison for the actual atlas constructions;
it does not attribute a separately numbered comparison theorem to Drinfeld.

The generic construction assumes arbitrary commutative rings O and R,
an O-algebra R, an arbitrary O-algebra ring D (possibly noncommutative),
and a supplied atlas on a fixed finite coordinate type in `Type`.
The coefficient algebra S and all its tests have universe v. The cover can
be infinite, and the image cover uses the original preimage choices from
`AtlasBaseChange`. No flatness or injectivity assumption is made.
The compatible-family carriers have universe v+1. Their D-actions are the
actions constructed by evaluation of actual chart endomorphisms in
`AtlasOrderAction`.

The special-atlas specialization assumes a nonarchimedean local field K,
a finite-dimensional central division K-algebra D, and a supplied embedded
subfield satisfying the explicit unramified full-degree condition. It uses
the actual order `IntegerRing K D`, the dimension given by the reduced degree,
and the geometric tangent conditions already carried by `SpecialAtlas`.
These are the hypotheses of `SpecialAtlasBaseChange`. No invariant-1/d
specialization or existence of the supplied subfield is proved here.

## Order-linearity of the constructed comparison

`OrderAction.baseChangeChartMap` copies the inverse of the actual
order-linear chart equivalence from `SpecialAtlasBaseChange`, replacing
its displayed function by the identity tuple function using the proved
application formula. Thus its linearity is for the full D-action on each
chart, rather than just the original O-action.

`OrderAction.toBaseChangePoints` uses the same full family restriction
function as `BasicAtlas.toBaseChangePoints`. Its addition law is inherited
from that map. For each d in D, chartwise D-linearity of
`baseChangeChartMap` proves the scalar equation at every test component.
Subtype and function extensionality give the equation for the entire
compatible family.

`OrderAction.baseChangePointEquiv` packages this D-linear forward map with
the previously constructed inverse `BasicAtlas.fromBaseChangePoints`.
Its inverse equations are the already proved full-family equations:
the inverse gives every original test algebra the induced S-action,
evaluates the image-chart family, and transports along the actual original
formal transition to the requested chart. No new inverse or comparison
is assumed. `baseChangePointEquiv_eq`, `baseChangePointEquiv_apply` and
`baseChangePointEquiv_symm_apply` identify the underlying forward map and
inverse with those constructions.

## Naturality, nilpotent tests and special atlases

`OrderAction.toBaseChangePoints_natural` reuses the underlying family
naturality equation, since the order-module coefficient maps use the same
actual precomposition functions. `baseChangePointFunctorIso` packages
the D-linear equivalences into a natural isomorphism from the original
point functor after restriction along R to S to the extended atlas's
point functor.

For any pi in R, `baseChangeNilpPointFunctorIso` precomposes this
isomorphism with `Nilp.forget S (algebraMap R S pi)`. The source evaluates
the original functor on restricted S-tests and the target is exactly the
new atlas's nilpotent-test functor. Neither R nor S is assumed to have
nilpotent pi for the unrestricted comparison.

The `LocalDivision.SpecialAtlas` declarations specialize the same
equivalence, forward component formula, constructed inverse, coefficient
naturality, natural functor isomorphism and Nilp restriction to the full
division-order action of a supplied special atlas. They introduce no
additional data or hypotheses and do not infer a height certificate
from specialness.

This unit concerns full compatible-family points of the constructed
image-cover atlas. Independence of preimage choices, iterated coefficient
coherence, refinement descent, presentation independence, a framing
object, moduli, representability and level structures remain separate
obligations.
