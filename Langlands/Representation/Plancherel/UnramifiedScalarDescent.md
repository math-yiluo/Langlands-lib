# Invariant rational scalars on finite character quotients

Author: Worker 200.

This derived construction presents a rational scalar fixed by a finite
subgroup of actual complex unramified characters using an invariant regular
numerator and an invariant nonzero regular denominator. Those two regular
functions descend to the character quotient. Their ratio is a continuous
function on a dense open subset of that quotient, and different presentations
give the same values wherever both denominators are nonzero.

## Source and provenance

The motivating source is J.-L. Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2
(2003), 235–333, DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`, with content SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
IV.1, printed pp.276–277 / PDF pp.42–43, defines polynomial and rational
functions on the complex twist orbit by pullback to `X(M)`. It also requires
representation-isomorphism naturality for an operator family. The beginning
of IV.3, printed p.285 / PDF p.51, obtains a rational composition scalar
`j_P` from generic induced irreducibility and Schur scalarity.

The finite norm construction here is an internal algebraic descent argument
supporting that orbit language. It is not a separately numbered source
theorem. The proof uses the existing regular character algebra, its proved
domain and dense-nonzero-locus properties, the existing function field and
translation automorphisms, finite products, and the topological quotient
universal property. No representation-theoretic conclusion from IV.3 is
assumed or established by this module.

## Parameters and translation convention

The generic constructions use any group `H : Type uG` with a topology, any
index type `I : Type uI`, and any family of positive characters
`ν : I → (H →* ℝ≥0ˣ)`. Write

```text
X = unramifiedCharacters ν
R = unramifiedRegularFunctions ν.
```

Here `X` is the existing group of continuous complex-unit characters trivial
on the common kernel of `ν`, with its inherited topology; `R` is the existing
evaluation-generated complex subalgebra of functions on `X`. A subgroup
`S : Subgroup X` acts by translation. The existing convention is

```text
(T_τ b)(χ) = b(τ * χ),
```

where `T_τ` denotes `unramifiedRegularTranslation ν τ`. The character group
is commutative even when `H` is not.

For the actual scalar construction, `F : Type u` has instances `Field F`,
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
The group scheme `L : GroupScheme (Spec (CommRingCat.of F))` has a supplied
rational-point topology. The explicit hypotheses are

```text
hp : Continuous (rationalValuationImageProjection L)
hL : GroupScheme.IsConnectedReductive L.
```

Specialize `ν` to all actual rational norm characters,
`νL = fun ψ => (rationalNormCharacters L ψ).toMul`, and write
`K = rationalUnramifiedFunctionField L hp hL`. This is the existing fraction
field of `R`. The field characteristic, splitness and quasisplitness are
unrestricted, and rank zero is allowed. The generic field, group and index
universes are not identified.

`S` is a subgroup of the full complex group `X`. It is not implicitly the
unitary stabilizer or the stabilizer of a representation. Only the finite
products and the existence theorem require an instance `Fintype S`.
The presentation structure, its quotient values, continuity and
presentation-comparison lemmas do not require finiteness.

## Finite denominator norm

For `b : R`, `unramifiedRegularNorm ν S b` is the product

```text
d = ∏ τ : S, T_τ b.
```

`unramifiedRegularNormCofactor ν S b` is the product of the same factors
with the identity element of `S` removed. The lemma
`unramifiedRegularNorm_eq_mul` separates the identity factor and proves
`d = b * c`, where `c` is that cofactor. This also covers the trivial
subgroup.

`unramifiedRegularNorm_invariant` proves `T_σ d = d` for every `σ : S`.
Translation distributes over the product, and
`T_σ (T_τ b) = T_(τ * σ) b`; the equivalence given by right multiplication
by `σ` permutes the factors.

For actual rational norm characters,
`unramifiedRegularNorm_ne_zero` proves `d ≠ 0` whenever `b ≠ 0`.
It supplies the imported domain instance
`rationalUnramifiedRegularFunctions_isDomain L hp hL`, uses injectivity
of each translation automorphism to show every factor is nonzero, and then
uses the finite-product nonvanishing theorem. This is nonzeroness in `R`,
not nonvanishing at every character.

## Invariant fraction presentations

`UnramifiedInvariantScalarPresentation L hp hL S f`, for `f : K`, consists
of the following data:

- A regular `numerator` and a regular `denominator`.
- `denominator_ne_zero`, asserting nonzeroness in `R`.
- `numerator_invariant` and `denominator_invariant` under every `τ : S`.
- `represents`, the equality
  `algebraMap R K numerator / algebraMap R K denominator = f`.

`unramifiedInvariantScalarPresentation_exists` assumes `Fintype S` and

```text
∀ τ : S, rationalUnramifiedFunctionFieldTranslation L hp hL τ.val f = f.
```

It concludes that this presentation type is nonempty. This fixedness
assumption concerns the existing fraction-field automorphism, not a
pointwise function with unspecified values at poles.

The implemented proof first writes `f = a / b` with a nonzero regular
denominator, using `IsFractionRing.div_surjective`. Set `d` to the norm of
`b` and `c` to its cofactor. Then `d = b * c`, `d ≠ 0`, and in `K`,

```text
algebraMap R K (a * c) = f * algebraMap R K d.
```

Apply fraction-field translation to this identity. The assumed fixedness
of `f` and proved invariance of `d` show that the image of `a * c` is
fixed. Compatibility of translation with `algebraMap` and injectivity of
that map give invariance of `a * c` in `R`. The required presentation has
numerator `a * c` and denominator `d`. No averaging or division by the
order of `S` is used.

## Quotient regular functions and scalar values

For arbitrary `ν` and arbitrary `S`, `unramifiedInvariantRegularDescend ν S b hb`
descends an invariant `b : R` to a function `X ⧸ S → ℂ`.
The quotient relation says `χ⁻¹ * ψ ∈ S`. Invariance under that element,
evaluated at `χ`, gives `b(ψ) = b(χ)` and makes the quotient lift
well-defined. `unramifiedInvariantRegularDescend_mk` states that its
value at the class of `χ` is exactly `b.val χ`.

`continuous_unramifiedInvariantRegularDescend` proves continuity using
`QuotientGroup.isQuotientMap_mk S` and the imported continuity theorem
for regular functions. This construction does not equip the quotient
with an algebraic-variety structure.

For an actual invariant presentation `p`, declarations in the
`UnramifiedInvariantScalarPresentation` namespace have the following
meaning:

- `regularRegion` is the subset of `X ⧸ S` where the descended
  denominator is nonzero.
- `value` is the ratio of the descended numerator and denominator,
  defined with domain `p.regularRegion`.
- `regularRegion_mk` identifies membership of the class of `χ` with
  `p.denominator.val χ ≠ 0`.
- `value_mk` identifies its value there with
  `p.numerator.val χ / p.denominator.val χ`.
- `regularRegion_isOpen` follows from continuity of the descended
  denominator. `continuous_value` uses continuous division on this
  subtype and its defining nonvanishing condition.
- `regularRegion_pullback_isOpen` and `regularRegion_pullback_dense`
  prove openness and density of its pullback to actual characters.
  Density uses `rationalUnramifiedRegular_dense_nonzero` for the
  nonzero regular denominator.
- `regularRegion_dense` descends that density through the quotient
  map, and `regularRegion_nonempty` projects a character in the dense
  nonzero locus.

Thus a fixed rational scalar has continuous values on a nonempty dense
open quotient region after choosing an invariant presentation.
There is no chosen value where that presentation's denominator vanishes.
Its regular region is not asserted to be maximal.

## Agreement between presentations

For two presentations `p` and `q` of the same `f : K`, `cross_mul` proves
the identity in the actual regular algebra

```text
p.numerator * q.denominator = q.numerator * p.denominator.
```

The proof maps to `K`, uses nonzero images of both denominators and
`div_eq_div_iff` on the two `represents` equalities, and then uses
injectivity of `algebraMap`.

`value_eq` proves equality of the two quotient values at any point
belonging to both regular regions. It chooses a character representative,
evaluates `cross_mul`, and divides by the two nonzero complex
denominators. Finally, `regularRegion_inter_dense` proves that this
common region is dense in `X ⧸ S`: the product of the two denominators
is nonzero in `R`, its nonzero locus is dense in `X`, and over `ℂ`
that locus is exactly the intersection of the two nonzero loci.
The common region is also open by the individual openness lemmas.

## Retained obligations

Applying this construction to the source's intertwining scalar still
requires an actual finite subgroup and proof of fixedness under that
subgroup. This module neither identifies `S` with the full complex
twist stabilizer nor compares its quotient with a representation orbit.
It supplies no restriction or density theorem for the unitary locus.
In particular, density in `X` alone does not assert density after
restriction to the unitary characters.

The original standard-intertwiner integrals and their naturality,
rational continuation, generic induced irreducibility, scalar
normalization, parabolic independence, nonvanishing and positivity,
the global source-normalized `j` and `μ`, Haar and orbit measures, and
the Plancherel and inversion theorems remain separate obligations.
This algebraic construction discharges none of those premises merely
by accepting them as structural data.
