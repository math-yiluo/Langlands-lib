# One cocharacter point contracts both dynamic radicals

This is an internal construction for the rational opposite Iwahori basis
proof. Its main result is
`Langlands.BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint`.
It applies to any affine group scheme over any nonarchimedean local field
`F : Type u`, with the canonical `rationalPointTopology`, and any actual
cocharacter `χ : 𝔾_m → G`. It does not require reductivity, splitness, a
root system, a building, or a finite type hypothesis.

The theorem constructs one rational point `g` before quantifying over any
compact set or identity neighbourhood. The point lies in the literal dynamic
centralizer `Z_G(χ)(F)` and commutes with every rational point of that
centralizer. For every compact ambient subset `C` contained in `U_G(χ)(F)`
and every identity neighbourhood `W`, all sufficiently large natural numbers
`n` satisfy

`g^n * c * (g^n)⁻¹ ∈ W` for every `c ∈ C`.

For every compact ambient subset of the literal inverse-cocharacter radical
`U_G(inverseCocharacter χ)(F)`, the same conclusion holds with conjugation
`(g^n)⁻¹ * c * g^n`. Both statements use this same `g`. This helper proves
these centrality and contraction facts; it does not itself construct compact
open subgroups or prove an Iwahori factorization.

## Evaluation and centrality

The selected definition `cocharPointHom` is the monoid homomorphism
`Fˣ →* RationalPoint F G.X` obtained by composing the intrinsic
`Gm.affinePointsEquiv` with `rationalPoints.map χ`.
`cocharPoint_eq` identifies its values with the Laurent-coordinate
`cocharPoint` from `CompactOpenContainmentProof`. The proof uses
`AffineLine.laurentAt_comp_laurentPoint` from
`Dynamic.DominantCombinationInclusions` and the product projection identity.
Consequently `cocharPoint_pow` follows from `map_pow`.

`cocharPoint_inverseCocharacter` applies the evaluation identity
`comp_inverseCocharacter` from `General.RationalOppositeParabolic`.
`cocharPoint_mem_centralizer` applies
`Dynamic.range_le_centralizer` from `Dynamic.NormalizedLimits` to the
cocharacter value. `commute_cocharPoint` evaluates the defining constant-orbit
identity `Dynamic.mem_centralizer` at a unit. The resulting identity is
`χ(t) * m * χ(t)⁻¹ = m`, which gives the asserted commutation.
These evaluation and centrality results require only that `F` is a field.

## Uniform contraction in the canonical topology

The published `DynamicUnipotentContainment.continuous_contraction` in
`CompactOpenContainmentProof` gives a continuous map
`F × U_G(χ)(F) → G(F)`. At nonzero `t` it is conjugation by `χ(t)`;
at zero it is the constant identity. Its proof uses the finite polynomial
coordinate expressions of the affine group and the canonical point topology.

`contraction_pow` identifies evaluation at `t^n` with conjugation by
`χ(t)^n`. If the field powers of a unit `t` converge to zero,
`tendsto_cocharPoint_pow_conj` gives joint convergence on
`atTop ×ˢ 𝓝 u` near each point `u` of the radical.

For a compact subset of the radical subtype,
`eventually_cocharPoint_pow_conj_mem` first pulls an identity neighbourhood
back along the continuous contraction at every `(0,u)`. It then applies
Mathlib's `IsCompact.eventually_forall_of_forall_eventually` to make the
field-parameter neighbourhood uniform on that compact set, and finally uses
the convergence `t^n → 0`.
`eventually_cocharPoint_pow_conj_mem_ambient` transfers an ambient compact
subset into the radical subtype using
`Topology.IsInducing.isCompact_preimage'`; its containment in the radical
ensures it is contained in the range of the subtype map. This transfer does
not add a closedness hypothesis.

## Choosing the single point

`exists_unit_tendsto_pow_zero` uses the nontrivial local-field valuation to
choose a nonzero `a` with valuation less than one, via
`Valuation.IsNontrivial.exists_lt_one`. With the additive uniform structure
provided by `IsTopologicalAddGroup.rightUniformSpace`, Mathlib's
`Valued.tendsto_zero_pow_of_v_lt_one` proves that the field powers of
`t = Units.mk0 a` converge to zero. The import
`Mathlib.Topology.Algebra.Valued.WithZeroMulInt` supplies this convergence
result.

The main theorem sets `g = cocharPoint χ t`. The centrality results give its
membership and commutation properties. The uniform-contraction result for
`χ` gives the first radical assertion. Applying that result to
`inverseCocharacter χ`, and rewriting its value as `g⁻¹`, gives the second.
The choice of `t`, hence of `g`, is independent of both compact sets and
identity neighbourhoods.

This construction and its packaging are derived from the named published
Lean results and Mathlib interfaces above; no additional external
mathematical assertion is introduced. The field's characteristic and the
cocharacter's triviality are unrestricted.
