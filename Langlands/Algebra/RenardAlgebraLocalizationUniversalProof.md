# B-linear universal property of the localized algebra action: proof

Authors: Worker 1019 and Worker 926, for task
`9998b1db-da89-430b-afbc-ce4b5110ef1e`, revision 1, under the Renard
whole-book parent `f5d1f399-a1f8-4ab5-a981-90b92abd4857`. Worker 926 wrote
and compiled a private probe proof of the target (theorem `probeUniversals`,
SHA256 `11f4d2c9b858bdd9bc5a225e9df1038cb23535724798698761b3e6729721b17f`).
Worker 1019 verified that hash and reused its route and most of its proof
steps. Worker 1019 split the proof into the named declarations below, ran the
checks and wrote this Markdown.

The module `Langlands/Algebra/RenardAlgebraLocalizationUniversalProof.lean`
imports the unchanged published statement module
`Langlands.Algebra.RenardAlgebraLocalizationUniversalStatements`. Its closed
theorem
`Langlands.Renard.AlgebraActionLocalization.universalPropertyStatements` has
exactly the type
`Langlands.Renard.AlgebraActionLocalization.UniversalPropertyStatements.{u, v, w, x}`.
It proves both the general ring statement and the field statement, with four
independent universes.

## Source and provenance

The target states the final sentence of Renard A.III.1, example 5, printed
p. 252 / PDF p. 258 of *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026 (registered source
`renard-2026-representations-groupes-reductifs-padiques`). That sentence says
the localization construction can be done with B-modules in place of
k-vector spaces. The source gives no separate proof. The statement's paired
Markdown records the formal encoding: B-modules are nonunital k-algebra
homomorphisms `B →ₙₐ[k] Module.End k V`, and B-module maps are actual
`LinearIntertwiner` objects. This proof adds no hypothesis to that statement.

## Implemented proof

All work happens in two helper theorems. They are stated for a commutative ring
`k : Type u`, a nonunital ring `B : Type v` with `[Module k B]`, and modules
`V : Type w` and `W : Type x`. The data are `a`, `ρ`, `ha`, `σ`, `c`, `hc`,
`f` and `hf`, exactly as in `UniversalPropertyStatement`. Write `g₀` for the
published scalar-linear factor
`factor a c.toLinearMap hc f.toLinearMap hf : Localized a →ₗ[k] W`. The
published `factor_intertwines` and `factor_comp_iota` give
`g₀ (localizedEnd a z) = c (g₀ z)` and `g₀ (iota a v) = f v`.

**`factor_map_localizedAction`: B-linearity of the factor.** This theorem
proves `g₀ (localizedAction a ρ ha b z) = σ b (g₀ z)` for every `b` and `z`.
The B-linearity of `g₀` is derived here; it is not assumed. Fix `b`. The
k-linear map `f ∘ₗ ρ b : V →ₗ[k] W` intertwines `a` with `c`. Indeed
`f (ρ b (a v)) = f (a (ρ b v)) = c (f (ρ b v))`, by `ha` and `hf`. Consider the
two maps `g₀ ∘ₗ localizedAction a ρ ha b` and `σ b ∘ₗ g₀` out of
`Localized a`. The proof shows that both satisfy the two hypotheses of the
published `factor_unique` for the map `f ∘ₗ ρ b`.

- The first map intertwines `localizedEnd a` with `c` by the published
  `localizedAction_localizedEnd` and the intertwining equation of `g₀`. It
  restricts along `iota a` to `f ∘ₗ ρ b` by the published
  `localizedAction_iota` and `g₀ (iota a v) = f v`.
- The second map intertwines `localizedEnd a` with `c`. This uses the
  intertwining equation of `g₀` and the B-linearity of `c`
  (`c.map_action b`). It restricts to `f ∘ₗ ρ b` by `g₀ (iota a v) = f v` and
  the B-linearity of `f` (`f.map_action`).

So `factor_unique` identifies both maps with the factor of `f ∘ₗ ρ b`.
Hence they are equal, and evaluating at `z` gives the claim. The proof only
uses that `c` is invertible in `Module.End k W`, through `hc`. It does not
need the B-linearity of the inverse of `c`.

**`universalProperty_of`: existence and uniqueness.** This theorem proves the
conclusion of `UniversalPropertyStatement` for fixed data. For existence,
the factor `g₀` and the previous theorem form an actual
`LinearIntertwiner (localizedAction a ρ ha) σ`. Its operator equation is
`factor_intertwines`. Its composite with `iotaIntertwiner a ρ ha` equals `f`
by `LinearIntertwiner.ext` and `factor_comp_iota`; the underlying map of
`iotaIntertwiner a ρ ha` is `iota a`. For uniqueness, let `g` be any
`LinearIntertwiner (localizedAction a ρ ha) σ` with both properties.
Evaluating `g.comp (iotaIntertwiner a ρ ha) = f` gives
`g.toLinearMap ∘ₗ iota a = f.toLinearMap`. The published `factor_unique` then
gives `g.toLinearMap = g₀`. `LinearIntertwiner.ext` turns this into equality
of intertwiners. So uniqueness holds among actual `LinearIntertwiner`
objects, as the statement requires.

**Closed theorems.** `universalProperty : UniversalPropertyStatement.{u, v, w, x}`
applies `universalProperty_of` to the quantified data.
`fieldUniversalProperty : FieldUniversalPropertyStatement.{u, v, w, x}` does
the same for a field `k`, using its commutative-ring instance. This type-checks
because the published `fieldLocalizedAction a ρ ha` is by definition
`localizedAction a ρ ha`. The extra field-statement instances
`[IsScalarTower k B B]` and `[SMulCommClass k B B]` are not used.
`universalPropertyStatements` pairs the two theorems.

The proof uses the published `Localized`, `iota`, `localizedEnd`, `factor`,
`factor_intertwines`, `factor_comp_iota`, `factor_unique`, `localizedAction`,
`localizedAction_iota`, `localizedAction_localizedEnd`, `iotaIntertwiner`,
`fieldLocalizedAction`, `LinearIntertwiner`, `LinearIntertwiner.ext` and
`LinearIntertwiner.map_action` by Lean name. It defines no new construction
and does not restate or re-axiomatize any of them.

## Scope

This proves the complete published aggregate. The algebra B and the actions
may be nonunital and noncommutative. Zero spaces and arbitrary source
operators `a` are allowed. No finiteness assumption is made. Kernel and
quotient descriptions, the converse characterization, the
surjective-canonical-map corollary, categorical packaging, localization
exactness and the C.II finite-localization proposition remain separate
parent obligations.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, service check
`6081dde8-9921-4ac3-81ee-e3e0021d299d` compiled the final module with no errors or
warnings. Inspection of `universalPropertyStatements` reported universe
parameters `u`, `v`, `w`, `x` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. These development checks are not
independent acceptance or publication.
