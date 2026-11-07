# Standard integral self-comparisons

Author: Worker 200.

## Provenance and purpose

This is a derived construction motivated by J.-L. Waldspurger, *La formule
de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*, IV.1,
printed pp.277–278 / PDF pp.43–44, DOI 10.1017/S1474748003000082.
The registered original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

On printed p.277 the source requires the operator square to commute under
the maps induced by an isomorphism of inducing representations. On
pp.277–278 it defines the standard integral on `(U ∩ U') \ U'` through
absolute convergence against every smooth contragredient functional and
existence of a representing vector in the original inducing space.
When these conditions hold for every input and group element, the
integral defines the actual ambient intertwining map. Theorem IV.1.1
subsequently proves convergence in a cone and rationality for finite-length
inducing representations.

The paired Lean module packages the existing actual full-domain integral
as a character family, proves transport of its parameter domain and its
original naturality square, and supplies the self-comparison witnesses
used by `ContinuedInductionOrbitScalar`. These are deductions from the
existing integral and transport theorems, rather than a separately numbered
source assertion or a proof of IV.1.1. The construction retains nonempty
open convergence regions as premises. It constructs neither those regions
nor rational continuation.

## Actual objects and hypotheses

`G` is a locally compact nonarchimedean group. The actual subgroups have
semidirect decompositions `P = MU` and, for target-valued operators,
`P' = MU'`, with closed radicals. The quotient is
`StandardIntertwining.QuotientSpace (U := U) U'`, namely the existing
possibly nonnormal left quotient by `U.subgroupOf U'`. Its measure is `qν`.

`H` is a topological group with a supplied topological group equivalence
`e : H ≃ₜ* M`. The family `ν : I → (H →* ℝ≥0ˣ)` is arbitrary. Write
`νM i = (ν i) ∘ e.symm` and
`χM = unramifiedCharactersHomeomorph e ν`. This is the existing character
transport, so `(χM χ)(m) = χ(e.symm m)`. For a canonical complex
`SmoothRep` object `A` of `M`, let `Aχ` be its twist by `χM χ`.
`UnramifiedLeviInduction` then applies the existing positive Levi
half-modulus normalization and actual smooth induction.

The domain-transport results need only the displayed measurable quotient
and its measure, besides the source group and decomposition hypotheses.
Target-valued families additionally retain the Borel structures of `U'`,
`U.subgroupOf U'` and the quotient, Hausdorffness of `G`, closedness of
`M`, compatible quotient-integration data for `qν`, and regular
right-invariant Haar measures `μU'` and `μI`. The predicate
`SquaredModulusCompatibility h hU h' hU'` is an explicit premise.
It is the existing identity of actual Haar conjugation characters; these
characters and the positive half-modulus are not chosen parameters.

The group universes `uH,uG`, character-index universe `uI`, and inducing
carrier universes `uV,uW` remain independent. Naturality permits two
different inducing carrier universes. No finite length, irreducibility,
admissibility, unitary restriction or topology on the inducing carriers is
needed for these deductions. This generic group construction imposes no
restriction on local-field characteristic, splitness or quasisplitness.
It does not itself realize the displayed structural or measure hypotheses
on every reductive rational-point group.

## The exact full-domain parameter region

`standardIntertwiningFullDomainRegion h hU U' e ν qν A` is the set

```text
Ω_A = {χ | StandardIntertwining.domain h hU U' Aχ qν = ⊤}.
```

The imported domain is the actual submodule of source vectors whose
scalar integrals are absolutely convergent against every smooth dual
functional at every `g`, with a representing vector in the original
inducing carrier. Thus membership in `Ω_A` includes both convergence and
representability for every source vector. It is not merely scalar
integrability or the domain of a separately supplied operator.

Given an actual equivariant equivalence `a : Aτ ≃ B`,
`standardIntertwiningFullDomainRegion_translation_iff` proves

```text
τ * χ ∈ Ω_A  ↔  χ ∈ Ω_B.
```

Its proof applies `domain_eq_top_iff_equiv` to
`transportedBaseTwistEquiv e ν τ χ a`, which identifies `A(τ*χ)` with
`Bχ`. Both sides use exactly the same quotient measure.
For a self-twist `a : Aτ ≃ A`,
`standardIntertwiningFullDomainRegion_self_translation` expresses this as
the equality of the preimage of `Ω_A` under `χ ↦ τ * χ` with `Ω_A`.
Its proof is set extensionality followed by the preceding equivalence.
Neither result asserts that `Ω_A` is open or nonempty.

## The original operator family and its naturality

For `χ : Ω_A`, `standardInductionIntertwinerFamily` is precisely
`fullSourceIntertwiner` for `Aχ`, using `χ.property` as its full-domain
proof. It is an actual ambient induced intertwining map from the
`P`-induction to the `P'`-induction. The construction keeps the supplied
quotient measure, compatible Haar measures and normalization data.

`standardInductionIntertwinerFamily_spec` applies
`fullSourceIntertwiner_spec`. For every source vector `f`, the evaluated
output function satisfies `StandardIntertwining.HasIntegral`: at every
`g` and every smooth dual functional `ℓ`, the scalar integrand is
integrable and

```text
ℓ((J_A(χ) f)(g)) = ∫ q, ℓ(f(u' g)) ∂qν,
```

where `u'` denotes a representative of the actual quotient element `q`.
The imported quotient descent makes this expression independent of that
representative. The theorem uses the original smooth-dual weak integral
and does not introduce a completed vector-valued integral.

`standardInductionIntertwinerFamily_natural` proves the original square
for `a : Aτ ≃ B`, `χ ∈ Ω_B`, and every `f` in the induction of `A(τ*χ)`:

```text
J_B(χ)(inducedMap_P(aχ) f)
  = inducedMap_P'(aχ)(J_A(τ*χ) f).
```

Here `aχ` is the actual `transportedBaseTwistEquiv`. The preceding domain
equivalence supplies `τ*χ ∈ Ω_A`. The proof applies
`fullSourceIntertwiner_natural` to `aχ.toIntertwiningMap` and evaluates
the resulting equality of intertwining maps at `f`. Thus the square
follows from proved naturality of the actual integrals.

## Both directions and every actual stabilizer element

For two decompositions `P₀ = MU₀` and `P₁ = MU₁`, the second section
retains separate quotient measures `q₁₀,q₀₁`, measures on their actual
intersections, quotient compatibility proofs, and squared-modulus
premises in the two directions. The radical Haar measures are shared
where they concern the same subgroup. Let `Ω₁₀,Ω₀₁` be the corresponding
full-domain regions and `J₁₀,J₀₁` the actual families just constructed.

Suppose `D₁₀ ⊆ Ω₁₀` and `D₀₁ ⊆ Ω₀₁` are nonempty ambient open sets in
`unramifiedCharacters ν`. For each genuine self-twist `a : Aτ ≃ A`,
`standardInductionSelfBaseChangeData` constructs
`InductionSelfBaseChangeData` for these families. Its comparison regions
are exactly `D₁₀,D₀₁`. Their supplied containments give original-domain
membership; the proved domain translation equivalence gives translated
membership. The two naturality fields are applications of the preceding
standard-family naturality theorem.

The forward and reverse comparison regions need not intersect. Moreover,
an arbitrary translated cone need not meet its original cone: it suffices
that each supplied `D` lies in the corresponding exact full-domain region,
which the self-twist has been proved to preserve. The construction makes
no claim of openness or nonemptiness of that entire region.

With `NonarchimedeanGroup H`,
`standardInductionSelfBaseChangeData_stabilizer` supplies a `Nonempty`
witness of this data for every element of the actual full twist
stabilizer of `SmoothRep.pullback e A`. That stabilizer is defined by
equality of actual smooth-representation isomorphism classes.
`stabilizerBaseTwistEquiv e ν τ` provides an actual equivalence `Aτ ≃ A`;
the constructor then gives the required witness. No finiteness,
irreducibility or admissibility hypothesis is needed for these witnesses,
and no compatible group law on the chosen equivalences is asserted.
The existing `InductionSelfBaseChangeData.toSelfBaseChangeData` can
subsequently transport them to the fixed compact carriers when its
separate compact-induction hypotheses are available.

## Remaining obligations

This unit proves the original standard-integral comparison squares and
their full-stabilizer witnesses conditional on full convergence on the
stated nonempty ambient opens and the displayed measure and modulus
data. Initial convergence, construction of those opens, rational
continuation, generic induced irreducibility and full-stabilizer finiteness
remain separate application obligations. It establishes no composition
scalar, opposite-parabolic identification, parabolic independence,
nonvanishing, positivity or source-normalized global `j`/`mu`.

Actual rational-point structural realizations and the remaining measure,
Schwartz, spectral and Plancherel conclusions are also separate. These
representation-theoretic and analytic premises do not become permitted
external structural inputs for completion of the whole Plancherel program.
