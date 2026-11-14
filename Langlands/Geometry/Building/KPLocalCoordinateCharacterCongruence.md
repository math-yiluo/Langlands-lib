# Coordinate characters and geometric congruence

This internal support unit constructs geometric characters from coordinate-field
characters and transfers the geometric congruence bounds to the coordinate
valuation. It does not prove `KPLocalTorusRootCommutatorStatement`.

For a tower of fields `k → E → Ω`, all in an arbitrary universe `u`, and a group
scheme `G/k`, `coordinateCharacterBaseChange` takes a rational character of
`G_E` to a subtype consisting of a rational character of the direct base change
`G_Ω` and its evaluation certificate. Its underlying character is the base
change from `E` to `Ω`, restricted along the inverse of `towerBaseChangeIso`.
For every `z ∈ G(k)`, the certificate states that this character on the extended
point is the image in `Ωˣ` of the original character on the extended `E`-point.
There is no finiteness, separability, affineness or torus hypothesis in this
construction.

The proof first identifies successive and direct point extension by the
coefficient-point comparison and the pullback projections. The inverse
identification follows from the isomorphism identity on rational points.
Character restriction and the published `rationalCharacterEval_extend` then
give the evaluation certificate. The character and certificate are constructed
together through a generic helper, retaining a small interface for later
specialization.

`coordinateCharacter_mem_unitFiltration_of_comparison` applies to additive
valuations `v` on `E` and `w` on `Ω` satisfying
`v(z) = w(algebraMap E Ω z)` for every `z`. If every geometric character of an
extended point lies in `addValuationUnitFiltration w r`, then every
coordinate-field character lies in `addValuationUnitFiltration v r`.
It tests the constructed character and transfers both its valuation-zero
condition and the lower bound on the value of its difference from one.
The depth `r : ℝ≥0` may be zero.

The local theorem `coordinateCharacter_mem_unitFiltration` takes a local field
`F`, a finite separable coordinate extension `E` of `K = UnramifiedClosure F`,
an explicit Henselian proof `hH` for the valuation ring of
`MaximalUnramified.valuation F`, and a commutative group scheme `T/K`.
For `t ∈ localGeometricCharacterCongruence F T r`, every rational character
`χ` of `T_E` satisfies

`χ(t_E) ∈ addValuationUnitFiltration (henselianSeparableAddValuation
  (MaximalUnramified.valuation F) hH E) r`.

The proof embeds `E` into `SeparableClosure F` using `IsSepClosed.lift`,
equips it with the induced scalar tower, and applies the generic transfer
lemma. The exact comparison in `KPLocalCoordinateValuationComparison` supplies
the required equality of valuations. The explicit Henselian hypothesis has a
published witness, `MaximalUnramified.valuationSubring_isHenselian`.

The provenance is internal: the construction and proofs are deductions from the
existing base-change comparisons, character-evaluation naturality, additive
unit-filtration definition and exact coordinate valuation comparison. No
unproved root-coordinate existence or building statement is assumed.
