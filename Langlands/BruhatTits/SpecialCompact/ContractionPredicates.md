# Contraction and cofinality for a simultaneous compact-open basis

This module defines the reusable proposition
`Langlands.BruhatTits.SpecialCompact.ContractionAndCofinality`. Its arguments
are a group `H` with a topology, subgroups `K M N Nbar`, chamber sets
`CA CAplus CAstrict : Set H`, and the threshold family `CAeps : ℝ → Set H`.
It packages the normalization and contraction clauses of Renard V.5.2(ii),
all of V.5.2(iii), and all of V.5.2(iv). It asserts no theorem about arbitrary
parameters and provides no existence proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 edition, V.5.2, printed page 123 / PDF page 129. The registered
source identifier is `renard-2026-representations-groupes-reductifs-padiques`.
The subgroup and filter packaging below is an internal translation of that
source. Renard cites [24], §2.1 for the structural theorem; no proof from that
reference or from the corrected Kaletha–Prasad construction is claimed here.

## Definitions and source map

All declarations below belong to
`Langlands.BruhatTits.SpecialCompact`. The helper `ambientConjugate g S`
is exactly the image of `S` under `x ↦ g * x * g⁻¹` in `H`. Every occurrence
of a compact factor in the formulas is the literal ambient intersection
`K ⊓ M`, `K ⊓ N`, or `K ⊓ Nbar`.

| Source label | Declaration | Formula and quantifiers |
| --- | --- | --- |
| S21, V.5.2(ii), normalization | `LeviIntersectionNormalization` | For every `m ∈ CA`, conjugation by `m` carries `K ∩ M` onto itself. |
| S21, V.5.2(ii), contraction | `WeakChamberContraction` | Every `m ∈ CAplus` sends `K ∩ N` into itself by conjugation; conjugation by `m⁻¹` sends `K ∩ Nbar` into itself. |
| S22, V.5.2(iii), powers | `StrictChamberExhaustion` | For every `m ∈ CAstrict`, `N = ⋃ n : ℕ, m⁻ⁿ (K ∩ N) mⁿ` and `Nbar = ⋃ n : ℕ, mⁿ (K ∩ Nbar) m⁻ⁿ`, as equalities of ambient subsets. |
| S22, V.5.2(iii), compact subsets | `UniformCompactContainment` | For every compact subset `Γ` of `N` there exists `ε > 0` such that every `m ∈ CAeps ε` satisfies `Γ ⊆ m⁻¹ (K ∩ N) m`; independently, for every compact subset of `Nbar`, all such `m` satisfy `Γ ⊆ m (K ∩ Nbar) m⁻¹` for a suitable positive threshold. |
| S23, V.5.2(iv), powers | `StrictChamberNeighborhoodBases` | For every `m ∈ CAstrict`, `mⁱ (K ∩ N) m⁻ⁱ` and `m⁻ⁱ (K ∩ Nbar) mⁱ`, indexed by `i : ℕ`, are identity-neighborhood bases in their respective radicals. |
| S23, V.5.2(iv), uniform clause | `UniformCompactOpenCofinality` | For every compact open subgroup `Γ` of `N` there exists `ε > 0` such that every `m ∈ CAeps ε` satisfies `m (K ∩ N) m⁻¹ ⊆ Γ`; independently the opposite-radical clause requires `m⁻¹ (K ∩ Nbar) m ⊆ Γ`. |

`ContractionAndCofinality` is the conjunction of the six named clauses, in
the table's order. Thresholds in the two radicals are quantified separately,
as in the source. They may depend on `K`, the parabolic parameters, and the
compact subset or compact open subgroup. There is no fixed strictly
contracting `m` before any uniform threshold: each threshold works for
**every** element of its threshold chamber. All powers are indexed by the
natural numbers including zero.

## Intrinsic topology and neighborhood-basis meaning

The topology on each subgroup type `U` is the topology induced from `H`;
no replacement topology is introduced. Its literal intersection with `K`,
viewed as a subgroup of `U`, is `Subgroup.comap U.subtype K`.
Compact subsets are `Γ : Set N` or `Set Nbar`, and compact open subgroups are
`Γ : OpenSubgroup N` or `OpenSubgroup Nbar` with `IsCompact` in those
inherited topologies. Their inclusions into `H` are the actual subtype maps.

The auxiliary proposition `ConjugatePowerNeighborhoodBasis K U m` requires
that every entire ambient conjugate `mⁱ (K ∩ U) m⁻ⁱ` lies in `U`.
Its second conjunct is `Filter.HasBasis` for `𝓝 (1 : U)`, with all natural
indices allowed and with basis sets

```text
{x : U | ∃ y : U, y ∈ Subgroup.comap U.subtype K ∧
                    (x : H) = m^i * (y : H) * (m^i)⁻¹}.
```

Thus every member is an identity neighborhood, and every identity
neighborhood contains a member. The explicit ambient containment prevents
silently truncating an ambient conjugate by intersecting it with `U`.
For the opposite radical the helper is applied to `m⁻¹`; hence its conjugates
are exactly `m⁻ⁱ (K ∩ Nbar) mⁱ`. Compactness, openness and the subgroup
structure of these conjugates follow in the intended topological-group
application from compact-open intersection factors and conjugation by a
normalizing element; they are not independently constructed by this module.

## Actual-group application and retained obligations

The actual-group target must first fix the same nonarchimedean local field,
connected reductive group, maximal split torus, minimal parabolic and special
maximal compact `K0` as the compact-package tasks. It must use the canonical
rational-point topology. It then quantifies **one** cofinal basis of compact
open subgroups `K` normal in that `K0`, and, for every `K` in that basis and
every actual standard parabolic, applies this predicate to its actual Levi,
unipotent radical and opposite radical. These data are not supplied by an
arbitrary good-position typeclass or by unrelated subgroup choices.

The chamber arguments must be the images of the actual central split
component of the Levi and its rational-character chambers. With the single
chosen uniformizer section of V.2.5, `CAplus` tests the restricted simple
characters by absolute value at most one, `CAstrict` by absolute value
strictly less than one, and `CAeps ε` tests them by absolute value strictly
less than `ε`. The last definition has no additional weak-chamber conjunct,
including when `ε > 1`. Empty character sets are allowed. This module takes
those sets as parameters; their actual construction and compatibility with
the published rational-character/valuation interfaces remain with the
actual-group wrapper.

S20, the single normal compact-open basis, is outside this predicate. The
ordered Iwahori multiplication and its intrinsic uniqueness/bijection laws
in S21 are also separate obligations of the wrapper. The inherited basis
for every standard Levi must use the same intersections with this common
basis and the same compatible split-component sections; the predicate
makes no new basis choice for a Levi. This smaller normal basis is distinct
from a chamber Iwahori. Proving its simultaneous construction and every
contraction/cofinality clause remains open here, both for valid explicit KP
data and for the separately retained general existence target.

The public declaration
`Langlands.BruhatTits.DynamicUnipotentCompactOpenContainmentStatement`
in `Langlands.BruhatTits.Unipotent.CompactOpenContainmentStatement` already
isolates the structural compact-open containment consequence. This module
does not restate it as a generic universal target. The S22-to-Jacquet
forgetting-openness deduction is a separate consumer and does not prove the
actual simultaneous basis.
