# Continuation for equivalent inducing representatives

Author: Worker 200.

## Internal provenance

This is an internal construction from the published actual standard-integral
families and their full-domain and compact-picture transport theorems. It
introduces no new translation of a numbered literature assertion. The direct
inputs are `StandardInductionSelfComparison`,
`StandardIntertwiningFullDomainTransport`, `CompactIntertwiningFamilies` and
`RationalUnramifiedOperatorContinuation`. The fixed linear transport in
`ContinuedIntertwiningNaturality` supplies the existing polynomial
precomposition and postcomposition interfaces.

The purpose is to construct continuation data for the actual standard
integral of an equivalent inducing representation from continuation data
for the first representative. The original integral square is proved using
the published integral naturality theorem. The second family's continuation
and its comparison square are therefore not additional inputs.

## Objects and hypotheses

Let `G` be a locally compact nonarchimedean Hausdorff group, with actual
subgroups and semidirect decompositions `P = M U` and `P' = M U'`.
The radicals, Levi and parabolics are closed. The two radical-modulus
unimodularity premises and the squared-modulus compatibility premise are
retained. A compact open subgroup `K` has factorizations `G = P K` and
`G = P' K`; both Levi projections are continuous.

The parameter group is `H`, with an actual topological group equivalence
`e : H ≃ₜ* M`. A family of continuous positive norm characters
`ν : I → (H →* ℝ≥0ˣ)` defines the existing unramified-character space.
Write `νM = ν ∘ e.symm` for the transported character family and `χM` for
`unramifiedCharactersHomeomorph e ν`. No dimension, openness or nonemptiness
condition is imposed on this parameter space.

The quotient measure `qν` is on the actual possibly nonnormal left quotient
by `U.subgroupOf U'` in `U'`. The ambient, intersection and quotient Borel
structures, compatible quotient integration, and regular right-invariant
Haar measures on `U'` and `U.subgroupOf U'` are explicit. The measure and
normalization data are fixed throughout transport.

Let `A` and `B` be canonical complex `SmoothRep` objects of the literal
Levi subgroup `M`, and let `φ : A.representation.Equiv B.representation`.
The universes of `H`, `G`, `I` and the two inducing carriers are independent.
No topology on the representation carriers, finite length, admissibility,
irreducibility or unitarity is needed. The generic construction imposes no
local-field characteristic, splitness or quasisplitness restriction. It
does not realize these displayed premises on reductive rational points.

## Full domains and original integral squares

Write

```text
Ω_A = standardIntertwiningFullDomainRegion h hU U' e ν qν A.
```

Membership means that the actual integral domain of the twist `Aχ` equals
the entire source induction. This includes absolute convergence against
every smooth-dual functional at every group element and existence of the
representing vector in the original inducing carrier.

`standardIntertwiningFullDomainRegion_equiv` proves `Ω_A = Ω_B`. It applies
`domain_eq_top_iff_equiv` at each parameter to `twistEquiv χ φ`. The quotient
measure stays the same. No convergence region is asserted to exist.

`standardInductionIntertwinerFamily_representative_natural` transports
full-domain membership along that equality and evaluates the published
`fullSourceIntertwiner_natural` identity. It proves the original square for
the actual ambient induced maps, at every parameter in the full domain.

`standardCompactIntertwinerFamily` restricts this exact family to the
fixed compact pictures using `compactIntertwiningOperator`. It is a family
on all of `Ω_A`, not a freely chosen family of compact linear operators.
For `S = compactInductionPictureEquiv h K φ` and
`T = compactInductionPictureEquiv h' K φ`,
`standardCompactIntertwinerFamily_representative_natural` proves

```text
J_B(χ)(S f) = T(J_A(χ) f).
```

It applies compact naturality to the already proved original square.
Both `S` and `T` are fixed, independent of the parameter.

## Constructed continuation

Suppose `p` is `RationalOperatorContinuationData Ω_A J_A`: one global
polynomial operator numerator `N_A` and one regular denominator `b`,
nonzero everywhere on `Ω_A`, with `N_A(χ) = b(χ) • J_A(χ)` there.
Polynomiality is pointwise in an input vector, with a finite expansion
whose size may depend on that vector; the denominator belongs to the
whole operator family.

`standardInductionRepresentativeContinuation φ p` constructs continuation
data for the actual family `J_B` on `Ω_B` by setting

```text
b_B = b,
N_B(χ) = T ∘ N_A(χ) ∘ S⁻¹.
```

The full-domain equality supplies nonvanishing of `b` on `Ω_B`.
Polynomiality follows by precomposition of `p.polynomial` with `S⁻¹`
and postcomposition with `T`. For the clearing identity, the proof applies
the actual compact square at `S⁻¹ f`, cancels `S S⁻¹`, and uses the original
clearing identity and linearity of `T`.

The denominator and regular-region lemmas are definitional equalities.
`standardInductionRepresentativeContinuation_continuedOperator` proves,
at every parameter of the original regular region,

```text
J_B,continued(χ) = T ∘ J_A,continued(χ) ∘ S⁻¹.
```

The proof expands the two reciprocal-denominator definitions and commutes
the fixed linear map `T` with scalar multiplication.

## Scope

This construction transports a supplied continuation; it does not establish
initial convergence or rationality, prove IV.1.1, or compare independently
chosen continuations. No scalarity, generic irreducibility, nonvanishing,
positivity, source-normalized `j` or `mu`, or Plancherel conclusion is
asserted. Those remain separate obligations of the standing program.
