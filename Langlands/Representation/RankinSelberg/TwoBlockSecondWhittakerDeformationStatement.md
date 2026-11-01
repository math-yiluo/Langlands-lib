# Entire standard-character deformation on the second lower-induced block

Author: Worker 15.

Module
`Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`.

This module states a derived transport of the published theorem
`Langlands.RankinSelberg.twoBlockWhittakerDeformation`. The new assertion
uses the standard Whittaker character and twists the second ordered block
by `|det|^u`. It is an internal consequence of the first-block deformation
in JPSS Section (4.5), rather than a literal second-block theorem printed
there. The proposition is a closed `Prop`-valued definition, with independent
field and original block-carrier universes `uF` and `uW`. This module does
not prove that proposition. The elementary identity at parameter zero is
proved.

## Original source and provenance

The registered source is `jpss-1983-rankin-selberg`: H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367–464. The retained scan is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The relevant original passages are:

- Section (4.5), printed pages 408–409, one-based PDF pages 43–44:
  the lemma deforms the first block by `α^u`, with `α = |det|`,
  preserves the initial Whittaker function, supplies one compact open
  right level for every complex parameter, and gives analyticity at each
  fixed group element. Page 409 applies the lemma with the inverse
  Whittaker character. Its subsequent integral argument uses additional
  support information.
- Section (6.1), printed page 427, one-based PDF page 62: in the
  adjacent-rank case the authors refer back to (4.5) when writing the
  second, rank-one block as `σ₀ ⊗ α^u` and reducing to large positive
  real `u`.
- Section (6.3), printed page 432, one-based PDF page 67: the proof
  again imposes that large second-block twist before its integral
  calculation.

All four printed pages were read visually from the scan, and its hash was
checked. There is no `notes/errata` directory in the admission Library; the
bounded source-specific search of the literature index and relevant public
notes found no registered JPSS erratum.

The Lean formulation follows the published first-block statement's
quantifiers and actual representation constructions. The second-block
placement and standard-character choice are justified by the transport
rationale below. The Section 6 references motivate this transport; they do
not assert the general all-parameter statement in the precise form used
here. No adjacent-rank factor identity is extracted in this module.

## The actual ordered family

Fix a prime `p`, a canonical p-adic field `F : PadicField.{uF} p`, and write
`T = F.canonicalTopologicalData`. The ambient group is
`G = Langlands.GeneralLinear (t + 1) F.Carrier`. For
`m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`, put
`B = succBlockShape m h`. The ranks of its ordered blocks are
`m 0 + 1` and `m 1 + 1`. All natural predecessors are allowed, including
zero, so either block can have rank one.

For independent dependent complex modules `W i : Type uW` and original
representations
`σ i : Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)`,
the two transparent abbreviations are exactly

```text
twoBlockSecondDeformedBlocks F m σ u i
  = Langlands.twist
      (T.determinantComplexPower (m i + 1) (if i = 1 then u else 0))
      (σ i)

twoBlockSecondDeformedInduced F m h σ u
  = F.canonicalNormalizedOppositeParabolicInduced B
      (B.blockTensor (twoBlockSecondDeformedBlocks F m σ u))
```

`determinantComplexPower` is the residue-normalized character `|det|^u`,
with `|ϖ| = q⁻¹`. The first block receives exponent zero, and only the
second block receives `+u`. Twisting retains each original carrier and
action multiplied by the displayed character. `B.blockTensor` is the
actual action of the block Levi on the dependent `PiTensorProduct`, in
the original order and with the original sizes.

The induced representation is the actual normalized smooth induction from
the standard lower block parabolic `B.oppositeParabolic`. For a lower
parabolic element `q` with Levi projection `a`, its sections satisfy

```text
f(q * x) = δ_B(a)^(-1/2) • (B.blockTensor σ_u)(a)(f(x)),
```

where `δ_B` is the upper block modulus. The ambient action is right
translation, `(ρ_u(g)f)(x) = f(x * g)`. Thus the original lower covariance
and its inverse half-modulus are retained. The family definition does not
replace these sections by a representation equivalent to them. The
section carrier can depend on `u`, because its covariance changes.

`twoBlockSecondDeformedBlocks_zero` proves equality with the original
block family at zero. Its implemented proof applies function
extensionality and simplifies the conditional with both branches zero,
`determinantComplexPower_zero`, and `twist_one`. Rewriting by this equality
identifies the zero-parameter induction with the untwisted normalized
lower induction, including its actual vector and functional spaces.

## The closed proposition

`Langlands.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement.{uF,uW}`
quantifies over every prime `p`, every such `F`, every supplied
`ψ : UnitaryAdditiveCharacter F.Carrier`, all `t`, `m`, `h`, all dependent
complex carriers `W i`, and every original family `σ i` as above.
`UnitaryAdditiveCharacter` includes nontriviality, continuity and unitarity.
Immediately after `F`, the proposition fixes
`letI := F.canonicalTopologicalData.topology`; all group openness and
compactness use the resulting matrix topology. No topology is placed on
the vector carriers.

The only representation-theoretic hypothesis is

```text
∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i).
```

This is the full published predicate: admissibility, finite generation of
`(σ i).asModule` over its group algebra, and a complex linear equivalence
between its whole standard-character functional space and `ℂ`. It allows
reducible representations. It is stronger than merely having a nonzero
Whittaker functional and does not assume irreducibility.

Write `ρ_u = twoBlockSecondDeformedInduced F m h σ u`. The proposition
takes every actual standard-character functional
`ℓ₀ : glFunctionals ψ t ρ_0` with `ℓ₀.val ≠ 0`, and every actual vector
`v₀` of `ρ_0`. It concludes that some scalar family
`Wu : ℂ → G → ℂ` satisfies all four clauses:

1. For every `g`, `Wu 0 g = ℓ₀.val (ρ_0 g v₀)`.
2. For every complex `u`, there are an actual
   `ℓ : glFunctionals ψ t ρ_u` with `ℓ.val ≠ 0` and an actual vector `v`
   of `ρ_u` such that `Wu u g = ℓ.val (ρ_u g v)` for every `g`.
3. There is one subgroup `K ≤ G`, open and compact, such that
   `Wu u (g * k) = Wu u g` for every `u`, `g`, and `k : K`.
   The subgroup is chosen before all parameters and group elements.
4. For every `g : G` and every `u : ℂ`,
   `AnalyticAt ℂ (fun z => Wu z g) u`.

Clause 2 is membership in an actual coefficient image of the stated
induction. Unipotent equivariance alone would not suffice. The functionals
and vectors may depend on `u`; neither their analytic dependence nor a
common identification of their carriers is asserted. The initial vector
may be zero even though the initial functional must be nonzero.

## Transport rationale for a later proof

This is a mathematical proof route, not an implemented Lean proof of the
proposition. Its representation comparisons must be constructed by that
later proof; none is a premise of the statement.

Let `η = ψ.scale (-1)`, let
`S_s = twoBlockDeformedInduced F m h σ s` be the published first-block
family, and let `χ_u = T.determinantComplexPower (t + 1) u`.

First change the additive character. The published
`isOfWhittakerType_standard_iff_inverse` transfers the full block type
from the standard character of `ψ` to its inverse. The identity
`standardCharacter_scale_neg_one` identifies that inverse with the
standard character of `η`. The published theorem
`twoBlockWhittakerDeformation` can therefore be applied with `η` and the
same original blocks. Its output character is the inverse character of
`η`, which equals the standard character of `ψ` by
`inverseStandardCharacter_scale_neg_one`. These identities identify the
functional subspaces without changing their underlying linear maps.
Rewriting both zero-block identities identifies `S_0` with `ρ_0`, so the
given `ℓ₀` and `v₀` supply the initial data, with nonzeroness preserved.
The theorem supplies a family `V_s(g)` of standard-`ψ` coefficients of
`S_s`, with `V_0(g) = ℓ₀(ρ_0(g)v₀)`, a compact open level `K₀`, and
pointwise entire dependence on `s`.

Use source parameter `s = -u`. A global twist of `S_{-u}` by `χ_u`
must be identified with `ρ_u` by an actual representation equivalence

```text
E_u : (Langlands.twist χ_u S_{-u}).Equiv ρ_u.
```

To construct it directly on lower-induced sections, use the published
`Langlands.Induction.smoothInductionTwistEquiv` with the smooth ambient
character `χ_u`. Its actual function map is
`f(x) ↦ (χ_u(x) : ℂ) • f(x)`, with inverse multiplication by
`χ_u(x)⁻¹`. The open kernel of `χ_u` supplies the smoothness of these
maps. It compares the global twist of smooth induction with smooth
induction of the restricted character twist of its covariance action.

The remaining comparison is on the actual lower covariance action.
The determinant of a lower block triangular element is the product of
the determinants of its ordered Levi blocks. Restricting `χ_u` to that
Levi therefore gives the product of the two block determinant powers.
The dependent tensor-action comparison distributes these scalars over
their original tensor factors. Combining twists adds exponents, and
for every `i : Fin 2` the resulting exponent is

```text
u + (if i = 0 then -u else 0) = (if i = 1 then u else 0).
```

The inverse upper half-modulus commutes with these scalar twists and
remains in the covariance. Inducing the resulting identity comparison
of the coefficient actions completes `E_u`. This requires equality or
an explicit intertwiner of the whole dependent tensor actions and
covariance representations, followed by the actual smooth-induction
equivalence. A commutative product of scalar characters alone does not
identify the induced representations.

The published
`TopologicalData.normalizedProductDeterminantTwistEquiv` in
`Induction.NormalizedProductCharacterTwist` performs this construction
for upper induction. A proof may instead combine it with the actual
lower-to-upper reversal `glOppositeProductReversal` from
`Induction.OppositeProductReversalProof`, transporting every ordered
size, carrier and block action and using determinant invariance under
the reversal conjugation. The direct lower construction described
above avoids that reindexing. Neither existing upper result is
silently treated as an already supplied lower-family comparison.

Define

```text
Wu u g = (χ_u(g) : ℂ) * V_{-u}(g).
```

Every upper unipotent element has determinant one, so `χ_u` is trivial
there. A standard-`ψ` functional of `S_{-u}` is consequently a
standard-`ψ` functional of its global twist on the same vector carrier.
If `V_{-u}` is its coefficient at `v`, transport the functional by
composition with `E_u⁻¹` and the vector by `E_u`. Intertwining then gives
exactly the displayed function as their coefficient for the actual
`ρ_u`. The transported functional is nonzero because `E_u` is a linear
equivalence. At zero, `χ_0 = 1` and `-0 = 0`; the displayed formula and
the initial value of `V` give the exact required coefficient of the
original `ℓ₀` and `v₀`.

For one level independent of `u`, restrict to
`K = K₀ ⊓ (T.determinantNorm (t + 1)).ker`. This kernel is the subgroup
where the determinant has normalized valuation zero, equivalently
`|det| = 1`. It is an open subgroup and hence closed; its intersection
with compact open `K₀` is compact open. All complex determinant powers
are one on it, for every parameter simultaneously. Multiplicativity
of `χ_u` and the `K₀` invariance of `V_{-u}` give
`Wu u (g * k) = Wu u g` on this single `K`.

Finally, for fixed `g`, the scalar `χ_z(g)` equals
`exp(z * log |det g|)` with a positive real base. It is entire.
Composing the entire function `s ↦ V_s(g)` with `z ↦ -z` and multiplying
by this exponential preserves `AnalyticAt ℂ` at every complex point.
No analyticity of an integral is used in this argument.

## Scope and remaining work

The proposition adds no induced full-type certificate, chosen comparison
equivalence, chosen entire family, support bound, integral analyticity,
irreducibility, central character, or factor identity to its hypotheses.
It preserves arbitrary positive two-block ranks, including rank-one
blocks, and independent `uF` and `uW`.

A separate successor must prove this exact proposition, including the
actual comparison `E_u` and coefficient transport. This statement and its
rationale do not prove determinant-slice integrability, analyticity of
slice integrals, specialization of polynomial-cleared identities, gamma
or L multiplicativity, or removal of a large-real-twist restriction from
a factor identity. Those conclusions need their own arguments.
