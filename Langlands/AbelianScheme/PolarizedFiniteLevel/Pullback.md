# Constructed pullback of actual polarized finite-level data

This internal construction assembles the actual pullback in the ordinary
moduli definition from the existing actual abelian-scheme pullback and
canonical dual comparison.

`DualWitness.pullback` derives changed existence from
`hasDualScheme_baseChange`, derives changed geometry via the canonical dual
parameter comparison, and pulls back the supplied inverse Poincaré bundle and
evaluation. The raw constructions are in `DualWitnessBaseChange`. No universal
dual existence or geometry assertion, or universal line-bundle-inverse
existence assertion, is an input.

`baseChangeIso` and `pullbackMap` wrap the existing canonical actual dual
comparison and dual-valued pullback. `parameterMap_pullbackMap` identifies
their underlying actual scheme map with `dualBaseChangeMap`.

`Datum.pullbackWith` allows a specified changed presentation. Its abelian
scheme is the actual pullback, its relative dimension is preserved by the
existing dimension transport theorem, and its polarization is transported
using the explicitly named `PolarizationBaseChangeStatement` in
`Prerequisites`. Constant degree follows from finite-flat native-rank
base-change and isomorphism invariance in `Degree`. Its full level is the
actual pulled-back ordered tuple, with the every-geometric-fibre basis
property already proved in `FullLevel`.

`Datum.pullback` supplies the derived `DualWitness.pullback` itself, giving
actual data along every scheme morphism. No moduli restriction operation is
supplied as an input. The constructions here work over arbitrary bases; the
final ordinary moduli functor restricts the object category to locally
noetherian universe-zero bases with the level invertible.
