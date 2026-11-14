# Lang correction for chambers with a specified closure point

This internal construction applies the group-theoretic quotient Lang correction
to chambers of supplied integer-valued building data. It preserves the concrete
closure witness required by `UnramifiedTwistedChamberThroughFixedPointStatement`.
No existence of a parahoric model or a reductive quotient is asserted here.

For `B : IntegerValuationBuildingData v G`,
`B.HasChamberClosurePresentation Y y` means that there are `g : G(k)` and
apartment points `x₀`, `x` such that:

- No affine root vanishes at `x₀`.
- `Y` is the image of the affine facet of `x₀` under `z ↦ g • apartmentMap z`.
- `x` belongs to the affine facet closure of `x₀`.
- `g • apartmentMap x = y`.

The supporting lemma `.isChamber` reads off the translated generic facet.
The lemma `.smul` multiplies the translating element on the left and retains
the same apartment points; its specified closure point becomes `a • y`.
These are algebraic presentation lemmas and make no topological closure claim.

`exists_stable_chamber_of_quotient_lang` takes a subgroup `P ≤ G(k)` fixing
`y`, a surjective homomorphism `q : P →* Q`, functions `θ : P → P`,
`F : Q → Q` and `τ` on the building, and the equations
`q (θ g) = F (q g)` and `τ (g • z) = θ g • τ z`.
It assumes Lang surjectivity for `F`, a chamber `Y₀` with the above closure
presentation through `y`, that the kernel of `q` preserves `Y₀` as a set,
and a supplied `h : P` with `τ '' Y₀ = h • Y₀`.
It concludes the existence of a chamber `Y` with `τ '' Y = Y` and a
closure presentation through the same `y`.

The proof gives the set of building points its induced `P`-action and applies
`Langlands.GroupTheory.exists_fixed_in_orbit_of_quotient_lang` to
`Y ↦ τ '' Y`. Point semilinearity implies set semilinearity by composition
of images. The resulting chamber is `g • Y₀`. Since `P` fixes `y`, the
translated closure presentation still has specified point `y`.
The quotient group, its Lang surjectivity and all geometric action hypotheses
remain explicit inputs.
