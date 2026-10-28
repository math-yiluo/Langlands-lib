# An inverse-character functional on the lower induction given by absolutely convergent integrals

This module defines one proposition,
`Langlands.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement`. It says
that the lower induced representation of the strict rank-one extension has an
inverse-character Whittaker functional `Λ` on its **whole** section space, and that
`Λ` is the ordinary integral of the scalar integrand wherever that integral converges
absolutely. The module proves nothing. It asserts no convergence for any section,
does not say that `Λ` is nonzero, and does not say that `Λ` is unique.

## Source and provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions*, Amer. J. Math. 105 (1983), registered as `jpss-1983-rankin-selberg`
(file SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The relevant place is the proof of Lemma (5.5), printed page 424 (one-based PDF page
59).

Formula (1) there defines the Whittaker functional `λ` on the induced space as a
limit, over an increasing sequence of compact open subgroups `V^ν`, of the integrals of
`μ(f(v)) θ̄(v)`, and refers to (4.5) for the existence of the limit. With
`W_f(g) = λ(σ(g) f)`, formula (3) is the integral `W_f(g) = ∫ f(vg; e) θ̄(v) dv` over
the opposite unipotent subgroup. The source substitutes it formally and then justifies
it by Fubini's theorem and Lebesgue's theorem for chosen `f` and `W`.

This proposition is a derived formulation. It keeps the conclusion that the source
uses, namely that `λ(σ(g) f)` equals the ordinary integral at every `(f, g)` where the
integrand is absolutely integrable. It does not ask for the limit (1) to exist for
every section. Instead it asks only for some functional on the whole section space with
the Whittaker property and with this integral formula on integrable data. That
requirement is weaker than formula (1) for every section. It is enough for the later
Fubini step of Lemma (5.5), which only uses the formula at absolutely convergent data.
The declaration name, the quantifier order and the transport through `asModuleEquiv`
are implementation choices. The sign of the character is the project's convention for
inverse-character functionals, explained below.

## Parameters

The proposition quantifies over:

- a prime `p` with `Fact p.Prime` and `F : PadicField.{uF} p`, with its canonical
  topology, valuative relation, local-field structure and the Borel measurable space
  on `F.Carrier`, all installed by `letI` after the quantifiers;
- a complex module `W` in an independent universe `uW` and a natural number `t`;
- an arbitrary quasicharacter `χ` of `F.Carrierˣ` and an arbitrary representation `σ`
  of `GL_(t+1)(F)` on `W`, with no smoothness, irreducibility or genericity
  hypothesis;
- a unitary additive character `ψ` and an inverse-character Whittaker functional
  `ℓ ∈ Whittaker.glInverseFunctionals ψ t σ`, with no nonvanishing hypothesis;
- a self-dual Haar measure `ν : LocalFactor.PadicAbelian.SelfDualHaar
  F.canonicalTopologicalData ψ`.

## Conclusion

There is `Λ ∈ Whittaker.glInverseFunctionals ψ (1 + t) (rankOneExtensionLowerModel F t χ σ)`
such that for every section `f : rankOneExtensionLowerSection F t χ σ` and every
`g : GL_(1+(t+1))(F)`:

if `y ↦ rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g y` is integrable for
`rowMeasure ν.val (t + 1)`, then

`Λ (I(g) f) = ∫ y, rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g y ∂ rowMeasure ν.val (t + 1)`.

Here `I(g) f` is written in Lean as
`rankOneExtensionLowerModel F t χ σ g ((rankOneExtensionLowerModel F t χ σ).asModuleEquiv f)`.
That is the actual induced action on the module carrier of the published lower model.

Membership of `Λ` in `glInverseFunctionals ψ (1 + t)` means
`Λ(I(n) v) = θ(n)⁻¹ Λ(v)` for every upper unipotent `n` of rank `1 + (t + 1)`, where
`θ(n) = ψ(Σ n_(i,i+1))` is the standard character. So `g ↦ Λ(I(g) f)` is a Whittaker
function for the inverse character.

## The objects used

All objects come from published modules. Nothing is defined here.

- `rankOneExtensionLowerModel F t χ σ` and its carrier
  `rankOneExtensionLowerSection F t χ σ` (module `RankOneExtensionAnalyticData`) are the
  published normalized opposite-parabolic induction of total rank `1 + (t + 1)` and its
  section carrier. The ordered lower factors are `σ` and the character
  `rankOneExtensionCharacter F χ` of `χ`, which acts on `ULift.{uW} ℂ`.
- `rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g` (module
  `RankOneExtensionStableJacquetData`) is the function
  `y ↦ ℓ(f(u(y) g)) · ψ(y_last)` on rows `y : Fin (t + 1) → F.Carrier`. Here
  `u(y) = [I, y; 0, 1]` is the upper cell, `ℓ(f(·))` is the published scalar
  contraction of the section, and `y_last = y (Fin.last t)`.
- `HarmonicAnalysis.rowMeasure ν.val (t + 1)` is the product measure
  `Measure.pi (fun _ => ν.val.measure)` on the row space. No other normalization is
  chosen.
- `Integrable` and `∫` are Mathlib's Lebesgue integrability and Bochner integral for the
  product of the Borel measurable spaces.

## Sign convention

The source integrates against the conjugate character `θ̄` because its `λ` is a
`θ`-Whittaker functional. Here both `ℓ` and `Λ` are inverse-character functionals, so
the integrand carries the positive factor `ψ(y_last)`. With this sign the integral is
formally `θ⁻¹`-equivariant. Take `n = [n', z; 0, 1]` with `n'` upper unipotent of rank
`t + 1`. Then `u(y) n = diag(n', 1) u(n'⁻¹(y + z))`. The change of variables
`y ↦ n'⁻¹(y + z)` preserves the row measure, and `ℓ` contributes `θ(n')⁻¹`. The last
coordinate contributes `ψ(z_last)⁻¹`. This computation is not part of the
proposition. It only explains why the stated sign is the consistent one.

## Relation to the stabilized construction

The published module `RankOneExtensionStableJacquetData` formalizes formula (1)
through compact-open stabilization. Its extension to the whole space requires the
hypothesis that every section stabilizes. The present proposition does not use that
construction. It needs no stabilization hypothesis, because it asks only for agreement
with the ordinary integral on absolutely integrable data.
