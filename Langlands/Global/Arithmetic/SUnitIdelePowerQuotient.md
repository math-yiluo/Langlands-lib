# Positive-power quotients of actual S-unit ideles

Authors: Worker 107, with the archimedean finite-index argument adapted from
the unpublished prescription draft by Worker 53 and Worker 1232.

This is an internal deduction from the existing actual S-unit idele product
model, the proved local power-index results, Mathlib's group quotients, and
the inverse function theorem at one. The arithmetic context is Artin and
Tate, *Class Field Theory* (AMS Chelsea, 2009), Chapter X, Section 2,
printed pp.77–79 (one-based PDF pp.86–88). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`;
the appended errata at PDF p.202 contain no relevant correction.
The topology adapters are derived constructions, rather than additional
arithmetic assumptions or claims that this proof follows the book's route.

For every number field `K : Type u`, finite set `S` of finite places, and
nonzero natural `m`, `sUnitIdeles_powerQuotient_profinite` proves that the
actual subgroup `IdeleSUnits.sUnitIdeles K S`, modulo the range of its
`m`th-power map and with the quotient topology, is Hausdorff, compact, and
totally disconnected. All infinite coordinates, including the real sign
components, are retained. This helper makes no assertion about the later
quotient by principal ideles.

The selected construction `piPowerQuotientEquiv` upgrades Mathlib's algebraic
power-quotient equivalence to a homeomorphism for an arbitrary product of
commutative topological groups. The product of the coordinate quotient maps
is an open continuous surjection. The quotient map from the product group
is also an open continuous surjection, and the algebraic equivalence
intertwines these two maps on every representative. The quotient-map
criteria give continuity and openness of the equivalence, hence a
homeomorphism. No finiteness of the indexing set is required.
`powerQuotientCongr` transports power quotients along a continuous
multiplicative equivalence, proving both directions continuous by descent
through the group quotient maps. `prodPowerQuotientEquiv` supplies the binary
product version by identifying its power range with the product of the
factor power ranges. The three elementary transfer lemmas then transport
Hausdorffness, compactness and total disconnectedness along these
homeomorphisms.

At a finite place, `isOpen_finite_powers` equips the actual completion with
its existing nontrivial norm and characteristic-zero structure. The
Library theorem `AdelicFunctoriality.range_pow_mem_nhds_one`, proved with
the inverse function theorem, makes the power range a neighborhood of one;
a subgroup containing such a neighborhood is open. For valuation units,
`localUnitPowers_eq_comap` proves that the power range is the preimage of
the ambient power range: if a power has valuation one, its root has
valuation one, since the exponent is nonzero. Continuity of subtype
inclusion gives openness within the valuation-unit group. Existing
`localPowers_finiteIndex` and `localUnitPowers_finiteIndex` give finite
quotients. The factor at a place of `S` is the top subgroup and is handled
by the corresponding preimage identity; elsewhere it is the valuation-unit
group. Thus every factor power quotient is finite and discrete, so is
Hausdorff, compact and totally disconnected.

At an infinite place, the same inverse-function argument gives openness.
The nontrivial norm is witnessed by the element two through the isometric
complex embedding. `infinite_power_finiteIndex` adapts the prescription
draft's positive real root argument. At a real place, either a unit or its
negative is an `m`th power, so the quotient is a surjective image of `Bool`.
At a complex place, the existing root theorem makes the power subgroup the
whole group. Actual finite quotients, together with openness, again give
finite discrete quotients; a numerical bound on the natural-number index
alone would not suffice to prove finiteness.

Finally, units of the whole infinite adele factor are continuously
multiplicatively equivalent to the product of the completion unit groups
via `ContinuousMulEquiv.piUnits`. The finite model is the product over all
finite places of `SUnitIdeleTopology.localFactor`. Applying the product
homeomorphisms gives the three profinite-space properties for the model's
power quotient. The continuous multiplicative equivalence
`SUnitIdeleTopology.productEquiv` then transports them to the actual
S-unit idele subgroup and its quotient topology. The field universe is
unrestricted throughout.
