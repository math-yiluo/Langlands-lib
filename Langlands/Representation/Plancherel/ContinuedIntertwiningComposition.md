# Composite rational continuations and continued composition identities

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1, printed p.283 / PDF p.49, treats the operators `J_{P'|P}(π)` as
rational functions of `π`. Its item (12) states
`J_{P'|P}(π) = J_{P'|P''}(π) J_{P''|P}(π)` when
`d(P',P) = d(P',P'') + d(P'',P)`, and refers to the proof of Theorem IV.1.1
for the identity of the convergent integrals. Item (10) of the same page
extends an identity from the convergence domain to all parameters
algebraically. This module isolates that extension step. It proves no
integral composition, no length condition and no convergence; those
remain inputs. The provenance is internal: the results compose the
published continuation, rational-uniqueness and compact-conjugation
interfaces.

## Composite continuation data

The first section is generic. `L` is a topological group, `ν` an indexed
family of positive characters of `L`, and `V`, `W`, `Z` complex vector
spaces in independent universes. Parameters are the continuous unramified
characters `unramifiedCharacters ν`.

Let `p` be a `RationalOperatorContinuationData` for a family
`A : Ω₀ → (V →ₗ[ℂ] W)` and `q` one for `B : Ω₁ → (W →ₗ[ℂ] Z)`. The original
regions `Ω₀` and `Ω₁` are arbitrary sets.

`RationalOperatorContinuationData.comp p q` is continuation data on
`Ω₀ ∩ Ω₁` for the parameterwise composite `B ∘ A`. Its denominator is the
product `q.denominator * p.denominator`, which is nonzero on the
intersection. Its numerator at every parameter is the composite of the two
numerators. Polynomiality is the published `IsPolynomialOperatorOn.comp`.
The clearing identity follows from the clearing identities of `p` and `q`
and commutativity of complex scalars.

`mem_comp_regularRegion` and `comp_regularRegion` prove that the regular
region of the composite is exactly the intersection of the two regular
regions. `comp_continuedOperator` proves that at every such parameter the
continued composite equals `q.continuedOperator ∘ p.continuedOperator`,
using `(ab)⁻¹ = a⁻¹ b⁻¹` for the two nonzero denominator values.

## Continued composition identity

The second section uses the actual character parameters of a connected
reductive group scheme `G` over a nonarchimedean local field of arbitrary
characteristic. A topology on `G(F)` is given, the rational
valuation-image projection is continuous (`hp`), and the norm family is
`rationalNormCharacters G`. The vector spaces are again arbitrary.

`RationalOperatorContinuationData.continuedOperator_comp_of_eqOn` takes
continuations `p`, `q`, `r` of families `A : Ω₀ → (V →ₗ W)`,
`B : Ω₁ → (W →ₗ Z)` and `C : Ω₂ → (V →ₗ Z)`. It also takes a nonempty open
set `D` contained in `Ω₀`, `Ω₁` and `Ω₂` on which `C = B ∘ A`. Its
conclusion holds at every parameter `χ` regular for all three
continuations:

\[
r^{\mathrm{cont}}(\chi) = q^{\mathrm{cont}}(\chi) \circ p^{\mathrm{cont}}(\chi).
\]

The proof applies the published `rationalUnramifiedOperator_eq_of_eqOn_isOpen`
on the triple regular region. Both sides are rational there: the left side
by restriction of `continuedOperator_rational`, the right side by the
published `IsRationalOperatorOn.comp`. They agree on `D` because each
continuation agrees with its original family there
(`continuedOperator_agrees`). The original regions need not be open, and
no other relation between them is assumed.

## Actual continued intertwiners

The third section uses the setting of `CompactIntertwiningContinuation`.
`L` is a connected reductive group scheme over `F` with a topology on
`L(F)` and `hp`. `G` is a locally compact nonarchimedean group. There are
three actual closed semidirect decompositions `P₀ = M U₀`, `P₁ = M U₁` and
`P₂ = M U₂` with a common Levi `M`, each with `IsUnimodularModulus`, a
closed parabolic, the factorization `G = Pᵢ K` for one compact open `K`,
and continuous projection. `e : L(F) ≃ₜ* M` identifies parameters, every
rational norm character of `L` is continuous, and `A` is a canonical
`SmoothRep.{0,uG,uV} ℂ M`. Write `Iᵢ(χ)` for the actual normalized
induction from `Pᵢ` of the twist of `A` by the transported character.

The inputs are three families of actual ambient intertwining maps:

* `J₁₀` from `I₀` to `I₁` on `Ω₁₀`;
* `J₂₁` from `I₁` to `I₂` on `Ω₂₁`;
* `J₂₀` from `I₀` to `I₂` on `Ω₂₀`.

They come with continuations `p₁₀`, `p₂₁`, `p₂₀` of their fixed
compact-picture conjugates and, for each, the nonempty open subset of its
region required by `continuedInductionIntertwiner`.

`continuedInductionIntertwiner_comp_of_eqOn` assumes a further nonempty
open `D` contained in all three regions with
`J₂₀(χ) = J₂₁(χ) ∘ J₁₀(χ)` for `χ ∈ D`. It proves that at every parameter
regular for `p₁₀`, `p₂₁` and `p₂₀` the continued actual intertwiners
satisfy

\[
J^{\mathrm{ext}}_{20}(\chi) = J^{\mathrm{ext}}_{21}(\chi)\,J^{\mathrm{ext}}_{10}(\chi),
\]

as an equality of ambient `Representation.IntertwiningMap` objects. The
compact composition hypothesis on `D` comes from the published
`compactIntertwiningOperator_comp`. The generic identity then gives the
compact equation for the three continuations. By
`continuedInductionIntertwiner_compact` this is the compact conjugate of
the ambient equation, and `compactIntertwiningOperator_comp_eq_iff`
returns the ambient equation. The three families need not be standard
integrals; the theorem applies to any actual intertwining families with
these continuations.

## Boundaries

No composition of actual standard integrals is proved on any open set.
The module establishes no ordered radical factorization, no length or
root-distance condition, no product convergence, nonempty convergence
region or continuation. Applying it to IV.1(12) requires those as separate
results. It proves no nonvanishing of any intertwiner and no statement
about the scalar `j`, parabolic independence, `mu` or the Plancherel
formula.
