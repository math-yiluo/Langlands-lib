# Proof of twisted-stable chambers through a twisted-fixed point

`unramifiedTwistedChamberThroughFixedPoint` proves the published proposition
`Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointStatement.{u}` exactly, at
an arbitrary universe `u`, with no added hypothesis. The statement's Lean/Markdown pair and
everything it imports are unchanged.

## Route

The proof is a one-line composition of three published Library theorems.

1. `unramifiedTwistedChamberQuotient` (module
   `Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientProof`) proves
   `UnramifiedTwistedChamberQuotientStatement.{u}` unconditionally. This is the finite-field
   quotient input: for the given data it supplies one `φ ∈ Aut(K/F)` whose integer powers meet
   every coset of the fixing subgroup of every finite-dimensional intermediate field, together
   with a `HasFiniteFieldChamberQuotient` structure at the point `y` for the twisted action of
   `φ`.
2. `unramifiedTwistedGeneratorChamber_of_quotient` (module
   `Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientReduction`) turns the quotient
   input into `UnramifiedTwistedGeneratorChamberStatement.{u}`. It proves the semilinearity
   identity `c φ • A.action φ (g • z) = (c φ * φ(g) * (c φ)⁻¹) • (c φ • A.action φ z)` and
   applies `HasFiniteFieldChamberQuotient.exists_stable_chamber` (Lang's theorem on the
   finite-field quotient). This gives a chamber through `y` that is stable under the twisted
   action `z ↦ c φ • A.action φ z` of the same `φ`, with its translated generic-facet and
   closure-point witnesses.
3. `unramifiedTwistedChamberThroughFixedPointReduction` (module
   `Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction`) proves the
   implication `UnramifiedTwistedGeneratorChamberStatement.{u} →
   UnramifiedTwistedChamberThroughFixedPointStatement.{u}`. For the chamber `Y = g · facet(x₀)`
   it chooses a finite-dimensional intermediate field `E`, the compositum of three fields. The
   first is the field on whose fixing subgroup `c` is trivial. The second has a fixing subgroup
   that fixes `g`. The third has a fixing subgroup that acts trivially on the character lattice
   of `T_K`, and hence on the apartment. The fixing subgroup of `E` therefore fixes `Y`
   pointwise for the twisted action. The set stabilizer of `Y` under the twisted action is a
   subgroup containing `φ` and this fixing subgroup, and the density property of `φ` makes it
   all of `Aut(K/F)`. The chamber and its presentation are those of step 2, and `IsChamber`
   follows from the presentation.

The Lean term is

`unramifiedTwistedChamberThroughFixedPointReduction
  (unramifiedTwistedGeneratorChamber_of_quotient unramifiedTwistedChamberQuotient)`.

The mathematical content and its source provenance (Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, 2023: the residual step of Proposition 9.10.1, (4) ⇒ (1), with Proposition 9.10.4)
are recorded in the Markdown files of those three modules and of their inputs.

## Downstream constraint

The proof uses, directly or through its imports, no proof of the consumers
`UnramifiedTwistedChamberStatement`, `LocalSimplyConnectedUnramifiedChamberStatement`,
`LocalSimplyConnectedUnramifiedIntegralTwistStatement`,
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`,
`LocalSimplyConnectedGaloisCocycleVanishingStatement` or
`LocalSimplyConnectedCocycleVanishingStatement`. In the module's transitive import closure, the
only file that names any of them is the target statement's own module, and only in a docstring.
