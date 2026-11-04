# Logarithmic character moduli on the actual Levi lattice

This is an internal construction derived from the existing rational-point
Levi family, its cocharacter-annihilator centralizers, the common uniformizer
section and the normalized logarithm. No additional literature assertion is
introduced. The field has arbitrary universe `u` and is a nonarchimedean local
field with its given valuation and topology.

`leviCentralUniformizerSection` restricts evaluation at the common uniformizer
to the integral submodule `cocharacterAnnihilator T (rootSet i ν I)` and lands
in the actual subgroup `leviCentralTorusPoints i ν I`. Membership follows from
`commute_uniformizerPowers` for a finite set of simple roots and an explicitly
supplied standard cocharacter for `I`. The map is a restriction of the existing
lattice-section homomorphism composed with the annihilator inclusion.
`leviCentralUniformizerSection_val` records its literal underlying torus point.
No splitness, monomorphism or character-kernel hypothesis is used in this step.

For an arbitrary complex-unit character `χ` of the full abstract center of the
literal Levi, `leviCentralTorusCharacterLog` composes the natural center map
with its positive modulus and `Plancherel.normLog` at the residue cardinality.
It is a homomorphism to multiplicatively written real addition.
`leviCentralLatticeCharacterLog` pulls it back along the uniformizer section
and writes the result as an additive real-valued function on the annihilator.
The homomorphism laws follow from multiplicativity of the character modulus
and additivity of `normLog`.

`uniformizerPowers_mem_center_of_all_pairings_eq_zero` assumes a finite
simple-root type, an existing standard cocharacter for the full index and the
equality `levi i ν Finset.univ = ⊤`. It applies the same commutation result to
the full index. A cocharacter annihilating every simple root therefore evaluates
to an element of the full abstract ambient center.
`leviCentralLatticeCharacterLog_eq_zero_of_all_pairings_eq_zero` additionally
retains containment of that ambient center in the selected Levi and unit
modulus of the character on its natural image. The center maps give the same
literal ambient point, so its modulus is one and its normalized logarithm
vanishes. These explicit hypotheses are retained, rather than conclusions
about abstract and scheme centers being identified.

`additiveLog_eq_mul_intCoordinate` is an elementary additive-group lemma.
If a real additive function vanishes on the kernel of an integer coordinate,
choose an element `ζ` with nonzero coordinate. The combination
`p ζ • x - p x • ζ` has coordinate zero. Applying the real function and dividing
by the nonzero integer coordinate gives
`ℓ x = (ℓ ζ / p ζ) * p x`.

`leviCentralLatticeCharacterLog_eq_mul_omittedRoot` applies this argument to
the complement of one simple root `α`. On the selected-root annihilator, a
zero `α` pairing means all simple-root pairings vanish. The preceding ambient
unit-modulus result supplies the kernel condition. The comparison element
`ζ` is explicitly supplied with a nonzero omitted-root pairing; its existence
is not asserted by this lemma. The real proportionality coefficient can be
positive, negative or zero. No sign alternative, arbitrary-torus-point transfer,
strict exponent statement or proof of the self-association target is claimed
in this supporting module.
