# Actual sheaf and stalk maps of bounded affinoid morphisms

Author: Worker 36.

## Meaning and scope

Let `K` be a complete normed ultrametric field, let `A` and `B` be the
positive-polyradius presented affinoid algebras of the imported development, and
let `φ : BoundedAlgHom K A B`. This module constructs the morphism
`locallyRingedSpaceMap φ` from the actual locally ringed spectrum of `B` to that
of `A`. Its underlying continuous map sends a bounded multiplicative seminorm
`y` to `comap φ.toBoundedRingHom y`. Its map of sheaves is the actual
compatible-rational-quotient-family pullback of `RationalOpenPullback`, with
scalars forgotten. Locality is proved on the genuine stalks over ordinary open
neighborhoods.

The construction retains arbitrary positive presentation radii, trivial
valuations, nilpotents and empty spectra. It adds no reducedness, strictness,
discreteness, nontrivial-valuation or inhabited-spectrum hypothesis. This unit
constructs each bounded map and its sheaf/stalk compatibility. Identity and
composition coherence, comparisons with other stored structure-sheaf models,
unrestricted analytic atlases and analytic etale sites are further obligations.

## Constructions and equations

`openSpectrumMap` is the continuous spectral map. The component of
`openAlgebraPresheafMap φ` at an ordinary open `U` is exactly
`OpenSections.pullback φ U`. The imported ordinary-open restriction equation
proves naturality. `algebraSheafedSpaceMap` equips this continuous map with the
constructed morphism of algebra-valued sheaves; no sheaf map is supplied as an
assumption.

`openStalkMap φ y` is Mathlib's induced stalk map of that sheafed-space
morphism. `openGerm_openStalkMap` identifies its value on every ordinary-open
germ with the germ of the actual pulled-back section.

For a rational source chart `d`, a rational target chart `e` and an actual
bounded chart restriction `g : e ⟶ RationalChart.pullback φ d`,
`completedResidueEvaluation_transport` identifies the two bounded algebra
homomorphisms from the rational quotient algebra of `d` to the completed residue
field at `y`: transport followed by evaluation equals evaluation at the image
point followed by `completedResidueComap K φ y`. The point must belong to `e`
and its image to `d`, as the declaration states. The proof uses the rational
presentation's uniqueness theorem and checks the original base-algebra
restriction equations.

`OpenSections.pointEvaluation_pullback` proves the resulting equality for every
actual section on every ordinary open. At the image point choose a rational
neighborhood inside `U`; at `y` choose one inside the preimage of its interior.
The imported local formula computes the pulled-back section in that target
quotient algebra. The transport equation then identifies its evaluation. These
are equations about the actual quotient-family sections, without replacing the
sections by functions on spectrum points.

`openStalkMap_residue` is the commutative square between the actual algebra-stalk
maps, the two `openStalkResidue` evaluations and the canonical completed-residue
map. The proof uses the stalk colimit's germ extensionality and the preceding
point-evaluation equality. `openStalkMap_isLocalHom` then reflects units: a germ
whose source residue is zero still has zero residue after pullback, contradicting
the proved nonzero-residue criterion for units whenever the pulled-back germ is
a unit.

`ringSheafedSpaceMap` applies the scalar-forgetting functor to the constructed
algebra-valued presheafed-space map. `openRingStalkMap` is its genuine induced
ring-stalk map. The equation `openRingStalkMap_eq` proves that it is the composite
of the inverse source `openStalkRingIso`, the scalar-forgotten `openStalkMap`,
and the target `openStalkRingIso`. The proof compares ordinary-open germs, using
the canonical scalar-forgetting colimit comparisons and the algebra-map germ
equation. `openRingStalkMap_isLocalHom` transfers unit reflection through these
actual ring isomorphisms. Finally `locallyRingedSpaceMap` packages that
ringed-space map with the proved locality of its stalk homomorphisms.

## Provenance

This is internally derived construction infrastructure. It combines
`RationalOpenPullback`, `RationalLocallyRingedSpace`,
`RationalOpenStalkResidue`, `RationalOpenLocalRing`, the canonical bounded
completed-residue maps in `Spectrum.ResidueField.Lift`, and Mathlib's
presheafed-space/stalk functors. The imported affinoid and rational-quotient
constructions carry their original-source provenance. This unit claims no new
translation of an original-literature assertion and assumes no analytic-space
morphism, stalk locality or cohomological output.
