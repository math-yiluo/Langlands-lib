# Local normalized parabolic orbit comparison

`PadicParabolicOrbitJacquetComparison` states the local comparison needed after
the support-filtration and exactness steps of the p-adic geometric lemma. This
module states the proposition and does not prove it.

For every prime, actual finite p-adic extension, compatible supplied topology,
positive rank and pair of block shapes `B, C`, choose a minimal permutation `w`.
Supply source and target block refinements and all three equalities identifying
their actual parabolic, Levi and unipotent subgroups with the intersections.
The conclusion is a natural isomorphism from
`parabolicOrbitJacquetFunctor T B C w` to the published
`geometricPieceFunctor T B C w S R hS.2.1 hR.2.1`.

The left side is the compactly induced orbit representation for
`P_B * w⁻¹ * P_C`, with conjugated source covariance, positive induction half
modulus and inverse target Jacquet half modulus. Radical coinvariants are taken
on the representation of `P_C` itself. The right side is normalized refined
Jacquet, inverse-conjugation transport between actual intersection Levis, and
normalized refined induction, followed by forgetting smoothness. The full
triples of intersection equalities are hypotheses; only their Levi components
are needed to type the target functor.

The natural isomorphism ranges over all smooth complex representations of the
source Levi and all their intertwining maps. There is no admissibility,
finite-dimensionality or finite-length restriction. Field and representation
universes remain independent, and the target carrier lies in their maximum.
The conclusion includes cancellation of the normalizing characters: it has no
residual character and no extra comparison, measure-scaling or surjectivity
hypothesis. No orbit ordering is required for this single-orbit statement.

## Source and derived formulation

The source is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 5.4 (printed 461) identifies each localized orbit functor with its
geometric piece; section 5.5 (printed 461–462) describes the comparison using
integration over the radical quotient; sections 5.6–5.17 supply the proof.
Section 6.4 (printed 468–469) specializes the construction to minimal
representatives and cancels the correction character, yielding the normalized
pieces of section 2.12.

This is a derived concrete GL formulation of that local comparison. The
published compact orbit induction is used as the input to radical coinvariants,
so identifying support quotients with this compact orbit model is a separate
Mackey comparison. The original proof factors the local comparison through
restriction, induction and coinvariant operations. A proof of this proposition
must supply the actual comparison and normalization cancellation; neither is
part of the definition of the new orbit functor. This proposition does not by
itself prove the fixed support-filtration theorem, ordering existence, or
existence of standard intersection refinements.
