# Opposite scalars of two parabolics from composition identities

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

In IV.3, printed p.285 / PDF p.51, `j_P` is the rational function with
`J_{P|P̄}(π') J_{P̄|P}(π') = j_P(π')` on the generic irreducibility locus.
Assertion (1) states that `j_P(π)` is independent of `P ∈ P(M)`. The proof,
printed pp.285–286 / PDF pp.51–52, takes `P' ∈ P(M)` and computes

```
j_{P'}(π) J_{P'|P}(π) = J_{P'|P̄'}(π) J_{P̄'|P'}(π) J_{P'|P}(π)
  = J_{P'|P}(π) J_{P|P̄'}(π) J_{P̄'|P̄}(π) J_{P̄|P'}(π) J_{P'|P}(π)
  = J_{P'|P}(π) J_{P|P̄}(π) J_{P̄|P}(π)
  = j_P(π) J_{P'|P}(π).
```

The first and last equalities are the definitions of `j_{P'}` and `j_P`.
The second and third equalities each apply IV.1(12), printed p.283 /
PDF p.49, twice. The source then concludes (1) without further comment.
That step cancels `J_{P'|P}`, which is a nonzero rational function by
IV.1(10) on the same page.

This module formalizes the computation and the cancellation. The four
composition identities, the two scalar identities and the nonvanishing of
`J_{P'|P}` at one parameter are explicit inputs. The module does not prove
IV.1(10) or IV.1(12), and it does not construct actual intertwiners. The
provenance is internal: everything is elementary linear algebra combined
with the published regular-function interfaces of
`RationalUnramifiedScalarField` and `RationalUnramifiedScalarCancellation`.

## Composition data

The first two sections are generic. `L` is a topological group and `ν` an
indexed family of positive characters of `L`. Parameters are the
continuous unramified characters `unramifiedCharacters ν`. `R` is an
arbitrary set of parameters. The four complex vector spaces `X₀`, `X₁`,
`X₂`, `X₃` lie in independent universes.

`ParabolicCompositionData R X₀ X₁ X₂ X₃` is a structure. Index `0` stands
for `P`, `1` for `P'`, `2` for `P̄'` and `3` for `P̄`. A field `J i j` is a
family `R → (Xⱼ →ₗ[ℂ] Xᵢ)`, from carrier `j` to carrier `i`, so that
`J₁₀` plays the role of `J_{P'|P}`. The eight families are `J₁₀`, `J₀₂`,
`J₂₃`, `J₃₁`, `J₁₂`, `J₂₁`, `J₀₃` and `J₃₀`. The four fields `comp₁₂`,
`comp₂₁`, `comp₀₃` and `comp₃₀` state, at every `χ ∈ R`, the four
instances of IV.1(12) used in the source:

* `J₁₂ = J₁₀ ∘ J₀₂`, that is `J_{P'|P̄'} = J_{P'|P} J_{P|P̄'}`;
* `J₂₁ = J₂₃ ∘ J₃₁`, that is `J_{P̄'|P'} = J_{P̄'|P̄} J_{P̄|P'}`;
* `J₀₃ = J₀₂ ∘ J₂₃`, that is `J_{P|P̄} = J_{P|P̄'} J_{P̄'|P̄}`;
* `J₃₀ = J₃₁ ∘ J₁₀`, that is `J_{P̄|P} = J_{P̄|P'} J_{P'|P}`.

The structure records only these identities. Nothing in it refers to
parabolic subgroups, length conditions or integrals.

## Pointwise cancellation

`ParabolicCompositionData.smul_J₁₀_eq` fixes `χ ∈ R` and complex numbers
`c`, `c'`. It assumes `J₀₃ χ ∘ J₃₀ χ = c • id` on `X₀` and
`J₁₂ χ ∘ J₂₁ χ = c' • id` on `X₁`. It concludes
`c' • J₁₀ χ = c • J₁₀ χ`. The proof is the displayed computation: rewrite
`c' • J₁₀ χ` as `J₁₂ ∘ J₂₁ ∘ J₁₀` and `c • J₁₀ χ` as
`J₁₀ ∘ J₀₃ ∘ J₃₀`, then substitute the four composition fields. Both
sides become `J₁₀ ∘ J₀₂ ∘ J₂₃ ∘ J₃₁ ∘ J₁₀`.

`ParabolicCompositionData.scalar_eq` makes the same assumptions and adds a
vector `v ∈ X₀` with `J₁₀ χ v ≠ 0`. It concludes `c' = c`, by evaluating
the previous identity at `v` and cancelling the nonzero vector.

## Nonvanishing on an open set

`IsRationalOperatorOn.exists_isOpen_apply_ne_zero` takes an open parameter
set `R`, a family `A : R → (V →ₗ[ℂ] W)` satisfying the published
`IsRationalOperatorOn R A`, and a point `χ₀ ∈ R` with `A χ₀ ≠ 0`. It
produces a set `D ⊆ R`, open and nonempty, and one vector `v` with
`A χ v ≠ 0` for every `χ ∈ D`.

The proof chooses `v` with `A χ₀ v ≠ 0` and, by the published
`exists_normalized_scalar_functional`, a linear functional `ℓ` with
`ℓ (A χ₀ v) = 1`. Rationality gives a regular denominator `b`, nonzero on
`R`, and a finite expansion of `b(χ) A χ v` in fixed vectors with regular
coefficients. Applying `ℓ` to the expansion gives one regular function `g`
with `g(χ) = b(χ) ℓ(A χ v)` on `R`. The set `D` is `R ∩ {g ≠ 0}`. It is
open because regular functions are continuous
(`continuous_unramifiedRegularFunction`), and it contains `χ₀` because
`g(χ₀) = b(χ₀) ≠ 0`. If `A χ v = 0` at some `χ ∈ D`, then `g(χ) = 0`,
which is impossible.

## Equality in the function field

The last section uses the actual parameters. `F` is a nonarchimedean local
field of arbitrary characteristic, and `G` a connected reductive group
scheme over `F` (`hG`) whose rational points carry a topology for which
the valuation-image projection is continuous (`hp`). The norm family is
`rationalNormCharacters G`, and the scalars lie in the published field
`rationalUnramifiedFunctionField G hp hG`. In the application of IV.3(1)
this group is the common Levi subgroup `M`, whose unramified characters
parametrize the twists `π ⊗ χ`.

`ParabolicCompositionData.functionField_eq` takes composition data `d` on
an open set `R`, rationality of `d.J₁₀` on `R`, and a point of `R` where
`d.J₁₀` is nonzero. It also takes two field elements `s`, `s'` and regular
functions `a`, `b`, `a'`, `b'` with `b` and `b'` nonzero on `R`, such that
`s = a / b` and `s' = a' / b'` in the field. Finally, on all of `R`, the
composite `J₀₃ ∘ J₃₀` is `a/b` times the identity and `J₁₂ ∘ J₂₁` is
`a'/b'` times the identity. The conclusion is `s' = s`.

The proof takes the open set `D` and vector `v` given by the previous
theorem for `d.J₁₀`. By `scalar_eq`, the values `a'/b'` and `a/b` agree on
`D`. Both quotients have published `ScalarPresentation`s on `R`, with
fractions `s` and `s'` by `toFunctionField_eq_div`. The published
`toFunctionField_eq_of_eqOn_isOpen` then identifies the two fractions,
because their values agree on the nonempty open set `D ⊆ R`.

## Scope

The theorems are conditional on all displayed inputs. In particular:

* The four composition identities are assumed on the whole set `R`. No
  instance of IV.1(12), no root-distance condition and no convergence of
  intertwining integrals is proved here.
* The scalar identities are assumed on the whole of `R`. No irreducibility
  locus, Schur argument or regular continuation is involved, so `R` must
  already be a set where both composites are the given scalars.
* Nonvanishing of `J₁₀` at one point of `R` and its rationality are inputs;
  IV.1(10) is not proved.
* No actual standard intertwiners, parabolic subgroups, compact subgroup
  or Haar measures appear. Hence no source-normalized `j`, independence of
  the actual scalars of `P ∈ P(M)`, nonvanishing, positivity, `μ` or
  Plancherel conclusion is claimed.
