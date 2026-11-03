# Finite character coefficients for compact-section Hecke entries

This is an internal construction from the existing actual compact double-coset
sections and finite Hecke sampling. It constructs finite character expressions
for the scalar entries used in a later fixed-level trace calculation. It does
not assert an induced-character regularity theorem or same-Levi comparison.

Fix a topological group `G`, a subgroup `P`, an actual complex representation
`σ` of `P`, and a compact open subgroup `K` of `G`. For `x : G`, put
`Hₓ = conjOpenSubgroup P K x`, the subgroup of `P` on which
`x⁻¹ * p * x` lies in `K`. Given a vector `v` fixed by `Hₓ` and a character
`χ : P →* ℂˣ` trivial on `Hₓ`, the existing
`fixedVectors_twist_eq_of_le_ker` places the same vector in the fixed space
for `twist χ σ`. `twistedDoubleCosetSection` applies the existing
`compactDoubleCosetSection` to this vector. Its values and support are those
of that actual section; it introduces no new function carrier.

`compactSectionTwistCoefficients P σ K x v L z` is a finitely supported
complex function on `P`. If `z = p * x * k` for some `p : P` and `k : K`,
it chooses such a factorization and returns the single coefficient
`L(σ(p)v)` at `p`. Otherwise it is zero. The choice is independent of `χ`.
The theorem `compactSectionTwistCoefficients_eval` proves that evaluating
this finite function by `Finsupp.linearCombination ℂ (fun p => (χ p : ℂ))`
equals `L` applied to the actual twisted section at `z`. In the factorization
case this follows from `compactDoubleCosetSection_apply` and linearity.
In the other case a nonzero section value would, by
`compactDoubleCosetSection_support_subset` and the actual left-quotient
relation, give the excluded factorization.

Now let `μ` be a measure finite on compact sets and `f` a Schwartz–Bruhat
function right invariant under `K`. Write `cᵢ, rᵢ` for the actual
`Hecke.fixedLevelActionSamples μ K f hf`.
`integratedCompactSectionTwistCoefficients` sums `cᵢ` times the preceding
finite coefficients at `y * rᵢ`. It still makes every choice before `χ`.
The intrinsic theorem `integratedCompactSectionTwistCoefficients_eval`
identifies its character evaluation with
`L(eval (integratedAction f section) y)` for the actual smooth induced
representation of `twist χ σ`.

The proof first checks that the compact section is a `K` fixed induced
vector, using `compactDoubleCosetSection_mul`. It applies
`Hecke.fixedLevelActionSamples_action`, then the linear functional obtained
by evaluation at `y` followed by `L`. Right translation evaluates the
sample action at `y * rᵢ`. The pointwise character-coefficient identity
finishes each summand.

The group and coefficient-carrier universes are independent. The
representation `σ` need not be smooth or admissible, and the induced carrier
has no topology or dimension restriction. No continuity or open-kernel
condition on `χ` is used beyond its explicit triviality on `Hₓ`.
The measure need not be Haar. Neither a compact quotient nor double-coset
representative cover is required for this single-section result.

The direct project dependencies are `CompactLocalSection`,
`Twist.AdmissibilityProof`, and `Hecke.FiniteSampling`; the used fixed-vector
twist lemma is algebraic and does not invoke the admissibility equivalence
proved in the same imported module. Mathlib supplies finitely supported
linear combinations and linear-map sum/scalar laws. This unit uses no
classification, character independence, geometric lemma, adjointness, or
cuspidal-support theorem.
