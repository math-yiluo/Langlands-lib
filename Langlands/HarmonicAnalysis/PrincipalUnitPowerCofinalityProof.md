# Principal-unit powers and uniform conductor bounds: proof

The module `Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityProof`
proves `Langlands.HarmonicAnalysis.principalUnitPowerCofinality.{uF}`, whose
type is exactly
`Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement.{uF}`.
The field universe `uF` is arbitrary. The statement module, the filtration
`T.principalUnits`, the valuation `T.discreteValuation`, the topology and
`T.multiplicativeConductor` are imported unchanged. The project imports are
the statement module, `Langlands.LocalField.Normalization.Proof` (for
`T.discreteValuation_uniformizer`) and
`Langlands.ClassField.Global.LocalPowerIndex` (for the generic power lemma).

The module adds three public theorems in the namespace
`Langlands.PadicField.TopologicalData`, all for an arbitrary prime `p`, an
arbitrary `F : PadicField.{u} p` and arbitrary topological data
`T : F.TopologicalData`. Each installs `T.topology`, `T.valuativeRel` and
`T.localField` as local instances, as the statement does.

Write `π = T.uniformizer`, `v = T.discreteValuation`, `O = T.Integers` and
`Uⁿ = T.principalUnits n`.

## Completeness of the canonical integers

`isAdicComplete_integers` states
`IsAdicComplete (maximalIdeal T.Integers) T.Integers`.
`T.Integers` is by definition the integer subring of the valuation
`ValuativeRel.valuation F.Carrier` of `T.valuativeRel`, which is Mathlib's
`𝒪[F.Carrier]`. Mathlib proves `IsAdicComplete 𝓂[K] 𝒪[K]` for every
nonarchimedean local field `K` in the section of
`Mathlib.NumberTheory.LocalField.Basic` that also assumes a uniform space
`[UniformSpace K] [IsUniformAddGroup K]`. The proof supplies the right
uniform structure `IsTopologicalAddGroup.rightUniformSpace F.Carrier` of the
topology `T.topology`, proves `IsUniformAddGroup` for it with
`isUniformAddGroup_of_addCommGroup`, and then closes the goal with
`inferInstance`. The conclusion is purely algebraic, so this auxiliary
uniform structure does not appear in the statement. No completeness or
Hensel hypothesis is added.

## Deep principal units are `m`th powers

`exists_principalUnits_subset_pow b m hm` proves the first clause: for
`0 < m` there is `N` such that every `u ∈ Uᴺ` equals `w ^ m` for some field
unit `w ∈ Uᵇ`.

The field has characteristic zero by
`Algebra.charZero_of_charZero (Padic p) F.Carrier`, so `(m : F.Carrier) ≠ 0`.
Hence `v m ≠ 0`, and `WithZero.exp_log` writes `v m = exp j` for an integer
`j`. Since `m` is an integer of the field, `v m ≤ 1`, so `j ≤ 0`. The proof
chooses

`N = 2 * (-j).toNat + (b + 1)`.

Thus `N` depends only on `T`, `b` and `m`. When `p` divides `m`, `j` is
negative and `N` grows accordingly; no prime-to-`p` condition is used.

Let `u ∈ Uᴺ`. From `T.discreteValuation_uniformizer` one gets
`π ≠ 0` and `v (π ^ (b + 1)) = exp (-(b + 1))`. So `c = π ^ (b + 1)` lies
in `O`. It lies in the maximal ideal because, after the strictly monotone
isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`, its
valuation is less than one, and
`Valuation.Integer.not_isUnit_iff_valuation_lt_one` identifies the
nonunits of `O`. Put `D = m ^ 2 * π ^ (b + 1)`. Then `D ≠ 0` and
`v D = exp (2 * j - (b + 1))`. The second membership condition of `u ∈ Uᴺ`
gives `v (u - 1) ≤ exp (-N)`, and `-N ≤ 2 * j - (b + 1)`, so
`t = (u - 1) / D` lies in `O`.

The published generic lemma
`Langlands.ClassField.Global.exists_one_add_mul_mul_pow_eq`, applied to the
ring `O`, the ideal `maximalIdeal O` (complete by the previous section),
the exponent `m`, the element `c` and `t`, gives `z ∈ O` with
`(1 + m * c * z) ^ m = 1 + m ^ 2 * c * t`. In the field the right side is
`1 + D * ((u - 1) / D) = u`.

Let `w = 1 + m * π ^ (b + 1) * z`. Since `v m ≤ 1` and `v z ≤ 1`,
`v (m * π ^ (b + 1) * z) ≤ exp (-(b + 1)) < 1`. The strict ultrametric
equality `Valuation.map_add_eq_of_lt_left` gives `v w = 1`, so `w ≠ 0`; the
proof takes the unit `Units.mk0 w`. It belongs to `Uᵇ`: its valuation is
one, and `v (w - 1) ≤ exp (-(b + 1)) ≤ exp (-b)`. Its `m`th power is `u`
in `F.Carrierˣ`, by `Units.ext` and the identity above.

## The uniform conductor threshold

`exists_conductor_bound_pow_ne_one b m hm` proves the second clause. Take
`N` from the first clause and set `A = N + 1`; this choice is made before
the character. For a quasicharacter `χ` with `A ≤ T.multiplicativeConductor χ`,
we have `N < T.multiplicativeConductor χ`, so the published
`T.exists_nontrivial_below_multiplicativeConductor χ N` gives `u ∈ Uᴺ` with
`χ u ≠ 1`. The first clause writes `u = w ^ m` with `w ∈ Uᵇ`, and `map_pow`
turns `χ (w ^ m) ≠ 1` into `(χ w) ^ m ≠ 1`. No conductor equality for
`χ ^ m` and no new character is used or constructed.

## The target theorem

`Langlands.HarmonicAnalysis.principalUnitPowerCofinality` introduces `p`,
the primality instance, `F` and `T`, installs the three local instances
from `T`, introduces `b`, `m` and `0 < m`, and pairs the two theorems above.
All positive `m`, including `m = 1` and multiples of `p`, and all levels
`b`, including `b = 0`, are covered. Characters are arbitrary elements of
`Quasicharacter F.Carrier`, with no unitarity or unramified-part condition.

The `lean_check` inspection of the target declaration reports level
parameter `uF` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The module contains no `sorry`, `admit` or new axiom.

## Provenance

This proof is derived, internal project work. Its route, a Hensel-type
lifting through the published generic power lemma, is not taken from a
specific source. The proposition is the auxiliary local-field prerequisite
recorded in the paired statement Markdown, motivated by H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions*,
American Journal of Mathematics 105 (1983), printed pages 392 and 404
(`jpss-1983-rankin-selberg`), with the conductor convention of J. Tate,
*Number theoretic background*, Corvallis Proceedings Part II (1979),
section 3.2.6, printed page 13 (`tate-1979-number-theoretic-background`).
Those sources do not state or prove this auxiliary proposition, and the
proof does not depend on them. Worker 726 wrote this module.
