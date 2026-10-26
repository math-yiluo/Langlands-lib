# Entire Whittaker deformation for two lower-induced blocks

Module `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`.

This module states the deformation lemma of JPSS (1983), Section (4.5),
printed pages 408–409. It works in the actual canonical p-adic setting, for
two blocks, in the inverse-character form that the source uses on page 409.
It contains:

- `Langlands.RankinSelberg.twoBlockDeformedBlocks`, a transparent `abbrev`
  for the deformed block family `σ_u`;
- `Langlands.RankinSelberg.twoBlockDeformedInduced`, a transparent `abbrev`
  for the deformed lower-induced representation `ρ_u`;
- `Langlands.RankinSelberg.twoBlockDeformedBlocks_zero`, a short proved
  identity `σ_0 = σ`;
- `Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement`, the
  proposition, a closed `Prop`-valued `def` at universe levels `uF` (field)
  and `uW` (block carriers).

The module states the lemma but does not prove it. It also makes no claim
about convergence, integral identities, Laurent series or multiplicativity.

## Source

- Source ID `jpss-1983-rankin-selberg`: H. Jacquet, I. I. Piatetski-Shapiro and
  J. A. Shalika, *Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983),
  367–464. File
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Exact locator: Section (4.5), the **Lemma** at the foot of printed page
  408, with its conclusions (1)–(3) continuing at the top of printed page
  409. Also the paragraph on page 409 that begins "We apply the lemma to
  `W' ∈ W(σ; ψ̄)`". These are zero-based PDF indices 42–43 (one-based PDF
  pages 43–44).
- Context: printed page 404, Section (3.1), defines
  `σ = Ind(G_t, Q; σ_1, …, σ_p)` with `Q` the **lower** standard parabolic
  subgroup of type `(t_1, …, t_p)`, and recalls Proposition (2.3) for
  Whittaker type of the induced representation. Printed page 408, Section
  (4.4), restricts to the case `r = t`, which is the setting of (4.5).

These pages were read visually from the registered scan. The file hash was
checked. No JPSS-specific erratum was found in the Library notes, the wiki or
the literature pointer index.

In the source the lemma reads as follows. Set
`σ_u = Ind(G_t, Q; σ_1 ⊗ α^u, σ_2)`. Then for every `W ∈ W(σ; ψ)` there is,
for each `u ∈ ℂ`, a function `W_u ∈ W(σ_u; ψ)` such that

1. `W_0 = W`;
2. there is a fixed open compact subgroup `K_0` with `W_u(gk) = W_u(g)` for
   all `g`, all `k ∈ K_0` and all `u ∈ ℂ`;
3. for each `g`, `u ↦ W_u(g)` is analytic.

Here `α = |det|`. In conclusion (2) the source writes `g ∈ G_r`, which is the
group `G_t` of the induced representation, because Section (4.5) treats the
case `r = t`. The source calls the lemma "essentially due to W. Casselman"
and cites [C-S, Section 2]. It calls the lemma a trivial consequence of
Proposition (3.2) of [F.S. I] and its corollaries, especially Corollary (3.4).
These references describe the proof that remains to be supplied later. They
are not premises of the Lean statement.

## Ranks and the actual family

Let `p` be prime, `F : PadicField.{uF} p`, and
`T = F.canonicalTopologicalData`. Every topological notion below uses
`T.topology` on `F.Carrier` and the induced matrix topology on
`GeneralLinear n F.Carrier`. That topology is `F.canonicalGeneralLinearTopology n`
by definition. The proposition fixes it once by
`letI := F.canonicalTopologicalData.topology` directly after `F`.

The source group `G_t` is `GeneralLinear (t + 1) F.Carrier`. The two source
blocks `G_{t_1}` and `G_{t_2}` are `GeneralLinear (m i + 1) F.Carrier` for
`i : Fin 2`, with `h : ∑ i, (m i + 1) = t + 1`. Thus all ranks are positive,
and rank-one blocks (`m i = 0`) are allowed. The block shape is
`B = succBlockShape m h` from
`Langlands.Representation.RankinSelberg.MultiplicativityStatement`.

For a complex parameter `u`, the family is built from published definitions:

```text
twoBlockDeformedBlocks F m σ u i
  = Langlands.twist
      (T.determinantComplexPower (m i + 1) (if i = 0 then u else 0)) (σ i)

twoBlockDeformedInduced F m h σ u
  = F.canonicalNormalizedOppositeParabolicInduced B
      (B.blockTensor (twoBlockDeformedBlocks F m σ u))
```

- `T.determinantComplexPower n u` is the character `g ↦ |det g|^u`, using
  the normalized absolute value (`determinantComplexPower_apply`). It is the
  source character `α^u`.
- `Langlands.twist χ π` multiplies the action by the scalar `χ(g)` on the
  same carrier.
- `B.blockTensor` is the actual block Levi acting on the dependent
  `PiTensorProduct` of the block carriers, each block acting on its own
  factor.
- `canonicalNormalizedOppositeParabolicInduced` is the published normalized
  smooth induction from the standard **lower** block parabolic
  `B.oppositeParabolic`. Its normalizing factor is the inverse square root of
  the upper block modulus, and `GL_(t+1)` acts by right translation on the
  smooth functions. This realizes `Ind(G_t, Q; ·)` with `Q` lower, as on page
  404. The upper-parabolic `canonicalNormalizedProductInduced` is not used, so
  no reversal of the blocks is needed.

**Sign and placement.** Only the first block (`i = 0`) receives the factor
`|det|^u`. The second block receives `|det|^0`, so it is unchanged up to the
identity `twist 1 = id`. This is the source's `σ_1 ⊗ α^u, σ_2`, with exponent
`+u`. On page 408 the strategy paragraph replaces `σ_1` by `σ_1 ⊗ α^(-u)` with
`u ≫ 0`. That is the same family after `u ↦ -u`, and the lemma itself is
stated with `α^u` for every `u ∈ ℂ`. The family is not
`shahidiTwistedPair`, which uses a different exponent convention.

**The case `u = 0`.** `twoBlockDeformedBlocks_zero` proves
`twoBlockDeformedBlocks F m σ 0 = σ` using `ite_self`, the published
`determinantComplexPower_zero` and `Langlands.twist_one`. Rewriting with it
identifies `twoBlockDeformedInduced F m h σ 0` with the untwisted lower
induction `F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ)`,
including its carrier and its functional spaces. The proposition itself is
phrased with the family at `0`, as the task specifies. A consumer who starts
from the untwisted induction can rewrite with this identity. A private
development check confirmed that the rewrite turns the proposition into the
expected statement for the untwisted induction.

## The proposition

`TwoBlockWhittakerDeformationStatement` quantifies over:

- every prime `p` with `[Fact p.Prime]` and every `F : PadicField.{uF} p`;
- every `ψ : UnitaryAdditiveCharacter F.Carrier` for the canonical topology,
  which includes continuity, unitarity and nontriviality;
- every `t : ℕ`, every `m : Fin 2 → ℕ` and every
  `h : ∑ i, (m i + 1) = t + 1`;
- every dependent family `W : Fin 2 → Type uW` of complex vector spaces and
  every family of block representations
  `σ i : Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)`.

The field and carrier universes `uF` and `uW` are independent.

**Hypotheses.** The only representation-theoretic hypothesis is the
published standard Whittaker type of each block:

```text
∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)
```

By `IsOfWhittakerType` (`RankinSelberg/AnalyticStatement`), this means:
admissibility, finite generation of `(σ i).asModule` over the group algebra,
and a linear equivalence of the whole space of standard Whittaker
functionals with `ℂ`. The block representations may be reducible. The
statement does not assume any of the following: Whittaker type of `ρ_u`, an
inverse-character type, irreducibility, a Whittaker-model equivalence, an
entire family, a uniform subgroup, analytic functionals, or any of the
conclusions.

**Data.** The statement takes every
`ℓ₀ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0)` with
`ℓ₀.val ≠ 0`, and every vector `v₀` in the actual carrier of `ρ_0`. The
carrier is the space of smooth functions of the lower induction. The source
`W ∈ W(σ; ψ̄)` is the coefficient `g ↦ ℓ₀(ρ_0(g) v₀)`, which is the
underlying function of `coefficientMap ρ_0 ℓ₀ v₀` in
`Whittaker/Algebraic`. By Proposition (2.3) of the source, `ρ_0` is of
Whittaker type, so every nonzero `ℓ₀` is a multiple of a fixed one, and the
coefficient functions of all such `ℓ₀` form exactly the Whittaker model. The
Lean statement does not use that fact. It requires the conclusion for
**every** nonzero `ℓ₀`.

**Conclusion.** There is a function
`Wu : ℂ → GeneralLinear (t + 1) F.Carrier → ℂ` satisfying all four
clauses:

1. **Initial value.** `∀ g, Wu 0 g = ℓ₀.val (ρ_0 g v₀)`, where
   `ρ_0 = twoBlockDeformedInduced F m h σ 0`. This is source conclusion (1),
   `W_0 = W`.
2. **Coefficient-image membership.** For every `u : ℂ` there are an actual
   `ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u)` with
   `ℓ.val ≠ 0`, and an actual vector `v` in the carrier of `ρ_u`, such that
   `∀ g, Wu u g = ℓ.val (ρ_u g v)`. Thus `Wu u` is the underlying function
   of `coefficientMap ρ_u ℓ v`. Equivalently, it lies in the coefficient
   image `coefficientModel ρ_u ℓ` of a nonzero inverse-character functional
   of the actual induced representation. This is the source's
   `W_u ∈ W(σ_u; ψ̄)`. It is stronger than inverse-unipotent equivariance of
   `Wu u`, which is not what is stated. The formulation goes through the
   surjective coefficient map. It does not use `modelEquiv`, which needs
   irreducibility. The carrier of `ρ_u` depends on `u` because the inducing
   representation changes. Therefore `ℓ` and `v` are chosen for each `u`.
3. **One compact open stabilizer for all parameters.** There is a single
   `K : Subgroup (GeneralLinear (t + 1) F.Carrier)` with
   `IsOpen (K : Set _)` and `IsCompact (K : Set _)` in the canonical group
   topology. For every `u : ℂ`, every `g` and every `k : K`,
   `Wu u (g * k) = Wu u g`. The subgroup is chosen before `u` and does not
   depend on it. This is source conclusion (2) with `K_0 = K`. The
   coefficient slice integrals on page 409 need this uniformity, so
   right-smoothness for each separate `u` does not replace it.
4. **Entire in the parameter.** For every `g` and every `u : ℂ`,
   `AnalyticAt ℂ (fun z => Wu z g) u`, using the usual topology on `ℂ`. So
   `u ↦ Wu u g` is analytic at every point of `ℂ`, that is, entire. This is
   source conclusion (3).

No topology is placed on the representation carriers. Every topological
condition concerns the group `GL_(t+1)(F)`, the field `F` or `ℂ`.

## Inverse-character specialization

The source states the lemma for `W ∈ W(σ; ψ)`, the standard character. On
page 409 it applies the lemma to `W' ∈ W(σ; ψ̄)`. The Rankin–Selberg
integrals pair a `ψ`-Whittaker function of `π` with a `ψ̄`-Whittaker
function of `σ`. The Lean statement is that inverse-character instance,
written with `glInverseFunctionals`, which is what the second Rankin–Selberg
input of the consumer needs.

This instance follows from the standard form applied to the character
`ψ.scale (-1) = ψ̄`, and published identities connect the two forms:

- `standardCharacter_scale_neg_one`
  (`RankinSelberg/FunctionalEquationStatement`) gives
  `standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n`.
  Hence the standard functionals for `ψ.scale (-1)` are exactly
  `glInverseFunctionals ψ n`, for `ρ_u` and for every block.
- `characterChangeFunctionalEquiv ψ π (-1)` (`Whittaker/CharacterChange`)
  is a linear equivalence
  `glFunctionals ψ n π ≃ₗ[ℂ] glFunctionals (ψ.scale (-1)) n π`. So the
  hypothesis `IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)`
  implies `IsOfWhittakerType (m i) (standardCharacter (ψ.scale (-1)) (m i)) (σ i)`.
  Admissibility and finite generation do not depend on the character.
  `characterChangeInverseFunctionalEquiv` gives the corresponding statement
  for inverse functionals.

A private development check compiled both facts: equality of the two
functional spaces, and the transfer of block type. So the block hypotheses
stay in the standard form that the parent Rankin–Selberg targets use. No
inverse-character type is assumed separately.

## Future proof obligations (not claimed here)

A proof must construct `Wu` from `ℓ₀` and `v₀`. It must produce, for each
`u`, a nonzero inverse-character functional on `ρ_u` and a vector of `ρ_u`
whose coefficients have the stated uniform level and are entire in `u`.
JPSS refer for this to Casselman–Shalika, Section 2, and to F.S. I,
Proposition (3.2) and Corollary (3.4). The deformed blocks stay of Whittaker
type by the published `isOfWhittakerType_twist_iff` in
`RankinSelberg/WhittakerTypeTwist`, since `|det|^u` is trivial on the
unipotent subgroup. Whittaker type of the induced `ρ_u` is the source's
Proposition (2.3). The present module neither asserts nor assumes any of
this.
