# Diagnostics for actual fixed-part comparison maps

This internal companion validates the constructions in
`Langlands.Algebra.NonUnitalModuleDualFixedPartComparison`, derived from
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.4.1, printed pp.22–23 / PDF pp.28–29, especially the
fixed-part comparison on printed p.23 / PDF p.29. The governing registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original nonunital module conventions are on printed pp.5–7 /
PDF pp.11–13, the recovered complex scalars on printed p.14 / PDF p.20,
and the fixed-part splitting on printed p.19 / PDF p.25. The registered
supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, does not change these maps. The 2026 edition governs.

The mathematical comparison comes from that source. Universe
specializations, competing-instance checks and singleton boundary cases
are derived internal diagnostics of the implemented interfaces; they
are not additional results asserted by the source. The core companion
explains the intrinsic module and linearity proofs.

The complete unapplied interface examples specialize both algebra and
carrier universe orders to `0, 1` and `1, 0`. They cover the opposite
corner equivalence, actual full fixed carrier and inherited complex
module, ordinary dual corner module, both complex-linear comparison
directions, both corner-linear comparison directions, and corner-linear
restriction and extension. Each example compares an entire declaration
with the displayed function type. The core module already checks the
general independent universe interface.

`CanonicalScalars` exercises the API with competing local structures.
It checks that an ambient complex module on M does not change the full
fixed carrier, the ordinary dual precomposition action or the canonical
inclusion/projection functional formulas. With competing full-dual and
nondegenerate-dual nonunital actions, the two fixed carriers still use
the exact named `fullAction` and `dualAction`, and the corner-linear
comparison maps still use `NonUnitalModuleCorner.fixedPartModule` for
those actions.

With competing complex modules on eM, the right fixed parts, and both
duals, the examples install the named recovered or inherited modules
explicitly. The private `fullComplexModule` helper freezes the usual
pointwise complex module on the precise full dual, recovered from the
original action on M. The full fixed scalar operation retains that
entire functional, and the right fixed scalar operation retains the
same functional through both subtype layers. The restriction and
extension corner maps have the published entire additive maps even
under those competing complex modules.

With a competing original left corner module, the ordinary dual action
and its complex scalar commutation use the published `fixedPartModule`
on eM. With competing corner modules on the two right fixed parts, the
examples explicitly select the published corner modules formed using
the original `fullAction` and `dualAction`. Both comparison directions,
restriction, extension and the full fixed scalar commutation have
these exact interfaces.

`ZeroIdempotent` verifies that all six complete maps, including the
complex-linear and corner-linear comparison maps and both corner
restriction/extension maps, are zero for the zero idempotent. The
private `fixedPartZero_subsingleton` proof uses the original
`NonUnitalModule.zero_smul` law to show that any two fixed elements
equal zero, then uses subtype extensionality. Applied to M and the two
precisely named original dual actions, it makes each fixed carrier a
singleton. The ordinary dual of the singleton fixed carrier is a
singleton by the existing linear-map instance. The six whole-map
equalities then follow from subsingleton elimination.

`ZeroModule` uses the actual singleton additive group
`PUnit.{uM + 1}` with the specified `NonUnitalModule.zero` action over
an arbitrary admissible A. The private `subsingleton_nondegenerate`
proof supplies the zero idempotent as a fixing witness. All four
whole-additive-map identifications are instantiated for arbitrary e,
so both complex comparison directions, both corner comparison
directions and restriction/extension remain available on this zero
module without an input complex module on it.

`ZeroAlgebra` instantiates the same whole-map identifications with
the actual singleton ring `PUnit.{uA + 1}` and singleton carrier
`PUnit.{uM + 1}`, their standard Mathlib structures and the specified
zero nonunital action. Its local-unit hypothesis comes from
`IsIdempotented.of_ring`; nondegeneracy again uses the zero
idempotent. The algebra and carrier universe parameters remain
independent. The singleton structures come from
`Mathlib.Algebra.Module.PUnit` and `Mathlib.Algebra.Ring.PUnit`.

No inverse, equivalence or naturality assertion is proved here.
The checks add no dimension, nontriviality, faithful-action,
anti-involution, unit-action or ambient complex-module assumption
to the constructions.
