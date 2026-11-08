# Equality of two continued opposite scalars from composition on open sets

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.3, printed p.285 / PDF p.51, defines `j_P` by
`J_{P|P̄}(π') J_{P̄|P}(π') = j_P(π')`. Assertion (1) states that `j_P` is
independent of `P ∈ P(M)`. The proof, printed pp.285–286 / PDF pp.51–52,
applies IV.1(12), printed p.283 / PDF p.49, four times:

* `J_{P'|P̄'} = J_{P'|P} J_{P|P̄'}`;
* `J_{P̄'|P'} = J_{P̄'|P̄} J_{P̄|P'}`;
* `J_{P|P̄} = J_{P|P̄'} J_{P̄'|P̄}`;
* `J_{P̄|P} = J_{P̄|P'} J_{P'|P}`.

It obtains `j_{P'} J_{P'|P} = j_P J_{P'|P}` and cancels `J_{P'|P}`, which is
nonzero by IV.1(10) on p.283. In the source these operators are rational
functions on all parameters, and IV.1(12) holds as an identity of rational
functions.

The structure `ParabolicCompositionData` of the module
`ParabolicCompositionScalar` records the four identities at every point of
one parameter set, and `ParabolicCompositionData.functionField_eq` performs
the cancellation when the composition identities and both scalar identities
hold on one open set and `J_{P'|P}` is nonzero at one of its points. This
module supplies those inputs from rational continuations. It assumes the
composition identities only on nonempty open sets, for the original
families. It replaces the nonvanishing input in two ways. If the scalar for
`P` is nonzero, nonvanishing of the continued `J_{P'|P}` is derived. In the
symmetric form, four further composition identities with the roles of `P`
and `P'` exchanged are assumed instead, and no nonvanishing hypothesis
remains. The provenance is internal: everything composes published
continuation, rationality and density interfaces with the modules
`ParabolicCompositionScalar` and `ContinuedIntertwiningComposition`, which
are independently approved candidates.

## Composition on an open set

The first section is generic. `H` is a topological group, `ν` an indexed
family of positive characters of `H`, and parameters are the continuous
unramified characters `unramifiedCharacters ν`. `V`, `W`, `Z` are complex
vector spaces.

`HasOpenComposition A B C`, for families `A : Ω₀ → (V →ₗ W)`,
`B : Ω₁ → (W →ₗ Z)` and `C : Ω₂ → (V →ₗ Z)` on arbitrary parameter sets, is a
`Prop`. It states that there is an open, nonempty set `D` with `D ⊆ Ω₀`,
`D ⊆ Ω₁` and `D ⊆ Ω₂`, such that `C(χ) = B(χ) ∘ A(χ)` for every `χ ∈ D`.
`HasOpenComposition.nonempty_first`, `nonempty_second` and `nonempty_third`
record that `Ω₀`, `Ω₁` and `Ω₂` are then nonempty.

## Actual parameters

From now on `L` is a connected reductive group scheme over a
nonarchimedean local field `F` of arbitrary characteristic (`hL`). Its
rational points carry a topology for which the valuation-image projection
is continuous (`hp`). Parameters are the actual unramified characters for
`rationalNormCharacters L`. In the application `L` is the common Levi
subgroup `M`.

`RationalOperatorContinuationData.continuedOperator_comp_of_hasOpenComposition`
takes continuations `p`, `q`, `r` of `A`, `B`, `C` and
`HasOpenComposition A B C`. At every parameter `χ` regular for `p`, `q` and
`r` it proves that the continued operators satisfy
`r(χ) = q(χ) ∘ p(χ)`. This is
`continuedOperator_comp_of_eqOn` of `ContinuedIntertwiningComposition`
applied to the open set of the hypothesis.

## Eight continued families

Four complex vector spaces `X₀`, `X₁`, `X₂`, `X₃` in independent universes
stand for the carriers attached to `P`, `P'`, `P̄'` and `P̄`, in this order,
as in `ParabolicCompositionData`. There are eight families on arbitrary
parameter sets, `Aᵢⱼ` going from `Xⱼ` to `Xᵢ`:
`A₁₀`, `A₀₂`, `A₂₃`, `A₃₁`, `A₁₂`, `A₂₁`, `A₀₃`, `A₃₀`. Each comes with a
continuation `pᵢⱼ` (a `RationalOperatorContinuationData`).

`parabolicRegularRegion L p₁₀ … p₃₀` is the intersection of the eight
regular regions. `parabolicRegularRegion_isOpen` proves it open, since each
regular region is open (published `regularRegion_isOpen`).

The four composition hypotheses are

* `h₁₂ : HasOpenComposition A₀₂ A₁₀ A₁₂`, that is `A₁₂ = A₁₀ ∘ A₀₂`;
* `h₂₁ : HasOpenComposition A₃₁ A₂₃ A₂₁`, that is `A₂₁ = A₂₃ ∘ A₃₁`;
* `h₀₃ : HasOpenComposition A₂₃ A₀₂ A₀₃`, that is `A₀₃ = A₀₂ ∘ A₂₃`;
* `h₃₀ : HasOpenComposition A₁₀ A₃₁ A₃₀`, that is `A₃₀ = A₃₁ ∘ A₁₀`.

Each holds on its own nonempty open set. The four sets need not meet.

`continuedParabolicCompositionData` is the `ParabolicCompositionData` on
`parabolicRegularRegion` whose eight families are the continued operators
`pᵢⱼ.continuedOperator`. Its four composition fields come from
`continuedOperator_comp_of_hasOpenComposition`.

## Equality of the scalars

The scalar of a continued opposite pair is the published
`continuedCompositeRationalScalar`. For continuations `p` of a family
`X₀ → X₃` and `q` of a family `X₃ → X₀`, a vector `v` and a functional `ℓ`,
it is the element of the published field
`rationalUnramifiedFunctionField L hp hL` given by the coefficient
`ℓ((q ∘ p)(χ) v)` of the continued composite. Write `j_P` for the scalar of
`p₃₀`, `p₀₃` with `v ∈ X₀`, `ℓ`, and `j_{P'}` for the scalar of `p₂₁`, `p₁₂`
with `w ∈ X₁`, `m`.

`continuedCompositeRationalScalar_eq_of_parabolicComposition` assumes:

* the four composition hypotheses above;
* nonemptiness of `Ω₃₀`, `Ω₀₃`, `Ω₂₁` and `Ω₁₂`, needed to form the two
  scalars;
* `ℓ v = 1`;
* `hsc`: at every parameter regular for `p₃₀` and `p₀₃`, the continued
  composite `p₀₃ ∘ p₃₀` is its extracted coefficient times the identity;
* `hsc'`: the same for `p₂₁`, `p₁₂` with `w`, `m`;
* `j_P ≠ 0`.

It concludes `j_{P'} = j_P`.

The proof takes regular presentations `j_P = a/b` and `j_{P'} = a'/b'` from
the published `continuedCompositeRationalScalar_spec`. Since `j_P ≠ 0`, the
numerator `a` is nonzero. The regular functions form a domain (published
`rationalUnramifiedRegularFunctions_isDomain`), so the product of `a` and the
eight denominators is nonzero. Its nonvanishing locus is dense (published
`rationalUnramifiedRegular_dense_nonzero`) and hence contains a parameter
`χ₀`. This `χ₀` lies in `parabolicRegularRegion`, and `a(χ₀) ≠ 0`. The four
regions `Ω₁₀`, `Ω₀₂`, `Ω₂₃`, `Ω₃₁` are nonempty by `h₃₀` and `h₀₃`, so their
denominators are nonzero too.

At `χ₀` the continued `J₁₀` is nonzero. Otherwise `J₃₀ = J₃₁ ∘ J₁₀` vanishes
at `χ₀`, so `J₀₃ ∘ J₃₀ = 0`. By `hsc` this composite is `(a/b)(χ₀)` times the
identity, and evaluating `ℓ` on its value at `v` gives `0 = a(χ₀)/b(χ₀)`, a
contradiction. The continued `J₁₀` is rational on `parabolicRegularRegion`
by restriction of the published `continuedOperator_rational`. Then
`ParabolicCompositionData.functionField_eq`, applied to
`continuedParabolicCompositionData` with the presentations above, gives
`j_{P'} = j_P`.

## Symmetric form

`continuedCompositeRationalScalar_eq_of_parabolicComposition_symm` takes in
addition four families `A₀₁ : X₁ → X₀`, `A₁₃ : X₃ → X₁`, `A₃₂ : X₂ → X₃` and
`A₂₀ : X₀ → X₂`, with continuations, and the four composition hypotheses
with the roles of `P` and `P'` (and of `P̄` and `P̄'`) exchanged:

* `h₀₃' : HasOpenComposition A₁₃ A₀₁ A₀₃`, that is
  `J_{P|P̄} = J_{P|P'} J_{P'|P̄}`;
* `h₃₀' : HasOpenComposition A₂₀ A₃₂ A₃₀`, that is
  `J_{P̄|P} = J_{P̄|P̄'} J_{P̄'|P}`;
* `h₁₂' : HasOpenComposition A₃₂ A₁₃ A₁₂`, that is
  `J_{P'|P̄'} = J_{P'|P̄} J_{P̄|P̄'}`;
* `h₂₁' : HasOpenComposition A₀₁ A₂₀ A₂₁`, that is
  `J_{P̄'|P'} = J_{P̄'|P} J_{P|P'}`.

It also requires `m w = 1`, and it does not assume `j_P ≠ 0`. The conclusion
is again `j_{P'} = j_P`. If `j_P ≠ 0`, the previous theorem applies. If
`j_P = 0` and `j_{P'} ≠ 0`, the previous theorem with the roles of the
indices `0 ↔ 1` and `2 ↔ 3` exchanged gives `j_P = j_{P'}`. If both vanish,
they are equal.

In the source setting the four further identities are also instances of
IV.1(12). For example `d(P, P̄) = d(P, P') + d(P', P̄)` for every
`P' ∈ P(M)`, because every reduced root of `A_M` in `Σ(P)` lies in exactly one
of `Σ(P̄')` and `Σ(P')`. This remark concerns the source and is not
formalized.

## Scope

* All composition identities are inputs. No integral, convergence domain,
  root-distance condition or instance of IV.1(12) is proved, and no family
  is required to be a standard intertwining integral.
* The scalar identities `hsc` and `hsc'` on the whole common regular regions
  are inputs. For actual induced representations they follow from the
  published `continuedInductionComposite_compact_eq_scalar` and a nonempty
  open locus of irreducibility; that application is not carried out here.
* No actual parabolic subgroups, compact subgroups, Haar measures or
  normalizations appear. In particular no statement about the source's
  `j`, its independence of normalizations, nonvanishing, positivity, `μ` or
  the Plancherel formula is made.
