# Compact-subgroup distribution formulas

This statement unit covers Renard II.3.11 on Hausdorff locally compact totally
disconnected groups. Every subgroup in these targets is an actual `Subgroup G`
with its induced topology and an explicit compactness proof. Openness and
countability are not assumed. The distribution, support, extended pairing and
convolution are the existing Library constructions.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locator: II.3.11, printed p.51 / PDF p.57, defining integral, Lemma and its last
proof sentence, Proposition (i)–(ii) and its stated consequences.

The declarations are in
`Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroup`.

- `ExtendedIntegralStatement` identifies the already constructed normalized
  subgroup distribution with the full displayed integral on locally constant
  functions. It uses `compactSupportPairing`, which descends a distribution to
  its actual compact topological support. The measure is Mathlib's
  `Measure.haarMeasure ⊤` on the actual compact subgroup with its Borel space.
  The normalization is the same as in `compactSubgroupHaar`.
- `DoubleCosetUniquenessStatement` sets `A` equal to the explicit compact
  convolution `e_K * δ_g * e_L`. It requires support in the literal set
  `K * {g} * L`, invariance under the original left action of `K` and right
  action of `L`, and mass one, evaluated as `compactSupportPairing A 1`.
  Every compactly supported distribution satisfying these same four conditions
  must equal `A`. Thus existence, uniqueness and the last identification in the
  source proof are all included; uniqueness is not made trivial by including
  the identification among the conditions on the competing distribution.
- `ProductStatement` states both `e_M = e_K * e_L` and
  `e_M = e_L * e_K` when the underlying set of the supplied compact subgroup
  `M` is exactly `K * L`. It does not assert that every product of two compact
  subgroups is a subgroup.
- `ConjugationStatement` uses the actual image subgroup
  `K.map (MulAut.conj g).toMonoidHom`. It asserts its compactness and the
  identity `δ_g * e_K * δ_(g⁻¹) = e_(gKg⁻¹)`.
- `IdempotenceAbsorptionStatement` states `e_K * e_K = e_K` and the two
  absorption identities when `K ≤ L`, with result `e_L` in both orders.

`Statements` is the conjunction of these five targets. These are closed
`Prop`-valued definitions and carry no proof claim. In particular the existing
function-valued compact-open normalized indicator identities do not supply
proofs of the arbitrary-compact-subgroup identities stated here. Their
compact-open density comparison belongs to II.3.12 and is a separate unit.
