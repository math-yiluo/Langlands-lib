# FML normalized valuation, lattices and unit filtration

This module supplies the valuation and subgroup constructors needed by the FML
conductor predicates. All public names below are in `Langlands.FML`; the field
has arbitrary universe `u`. The hypotheses are `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`, except that Lean omits
unused instances from the valuation-ring and unit-group abbreviations.

## Definitions and conventions

`normalizedMultiplicativeValuation F : Valuation F ℤᵐ⁰` maps the canonical
`ValuativeRel.valuation F` along
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F`. Writing this valuation
as `v`, `ord F : AddValuation F (WithTop ℤ)` has values

\[
\operatorname{ord}(x)=
\begin{cases}
\top,&v(x)=0,\\
-\log(v(x)),&v(x)\ne0.
\end{cases}
\]

Thus zero has infinite order. `ord_zero`, `ord_one`, `ord_eq_top_iff`,
`ord_ne_top_iff`, `ord_neg`, `ord_mul` and `ord_add` expose the bundled
valuation laws. In particular `ord_add` is the lower bound by the minimum of
the two summands' orders; it does not claim equality when cancellation occurs.
`ord_le_ord_iff` and `ord_lt_ord_iff` identify comparison of additive orders
with reversed comparison in the supplied valuative relation.
`ord_nonneg_iff_mem_integer` identifies nonnegative order with membership in
the canonical valuation ring.

`ringOfIntegers F` abbreviates `(ValuativeRel.valuation F).integer`.
For every `n : ℤ`, `lattice F n : Submodule (ringOfIntegers F) F` has carrier
`{x | (n : WithTop ℤ) ≤ ord F x}`. `mem_lattice` is the defining membership
equivalence. Negative depths are allowed.

`unitGroup F : Subgroup Fˣ` is the unit group of the canonical valuation
subring, embedded in the field units. `ord_unitGroup` proves that such a unit
has additive order zero. For `unitFiltration F : ℕ → Subgroup Fˣ`,

- `unitFiltration F 0 = unitGroup F`;
- membership in `unitFiltration F (n + 1)` means membership in `unitGroup F`
  together with `(u : F) - 1 ∈ lattice F ((n + 1 : ℕ) : ℤ)`.

These are exposed by `unitFiltration_zero` and `mem_unitFiltration_succ`.
In particular the zero layer is all integral units, and each positive layer
retains the integral-unit condition explicitly.

## Implemented supporting proofs

The private conversion from multiplicative to additive order sends zero to
infinity, reverses inequalities, and converts multiplication to addition.
The `AddValuation.of` constructor uses these facts and the multiplicative
valuation's bound on sums. The comparison lemmas follow by the order
isomorphism and `Valuation.Compatible.vle_iff_le`.

Lattice closure under addition follows from `AddValuation.map_le_add`.
Scalar closure uses nonnegative order of integral scalars and `ord_mul`.
For positive unit layers, the identity
`u * v - 1 = u * (v - 1) + (u - 1)` proves product closure, using the order-zero
property of integral units. Inverse closure uses
`u⁻¹ - 1 = -(u - 1) * u⁻¹` and the bundled inverse law. These short constructor
proofs replace the upstream dependency on its larger congruence API.

## Source and modifications

Adapted by Worker 20 from Fukuhiro Ueda, *epsilon_FML*, commit
`0b4159be50e1bd45ddff1de4280399576a3e2024`, licensed under Apache-2.0.
The original license is retained unchanged in [LICENSE](LICENSE).
The registered original is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the source prefix is
`fukubillueda-web--epsilon_FML/source/LanglandsFirstMainLemma/`.
Precise source locations relative to that prefix are:

- `LocalField/Valuation.lean`, lines 20–55, 71–142 and 183–209:
  the normalized valuation, additive-order construction and retained laws.
  Lines 328–335 define the congruence relation expanded in the positive layers.
  File SHA-256:
  `d1d40703fde462c5e1023e8aff759ab1956b8111ce1272e8f5c994511a857522`.
- `LocalField/Lattices.lean`, lines 67–88: the valuation ring, submodule
  constructor and membership equivalence. File SHA-256:
  `ff37ebdfbdf904bbcf7d1b0fc0156abe7ca53bc14a63234f23052baf4e063e70`.
- `LocalField/UnitFiltration.lean`, lines 19–24 and 67–94: the unit group,
  its relation to order zero, and the subgroup constructors. Only the forward
  implication of the order-zero characterization is retained, with a direct
  proof from `Valuation.mem_unitGroup_iff`. File SHA-256:
  `9421870db84fc04026fa9e90fbdb4c3c94385c14f78c25b9e655ed2ebc79f019`.

The port changes the namespace, makes the universe explicit, exposes the
previously private normalized multiplicative valuation, and combines the
needed definitions from three upstream modules. It uses
`Mathlib.NumberTheory.LocalField.Basic`, `Mathlib.Tactic.Ring` and
`Mathlib.Tactic.FieldSimp` instead of upstream `Prelude.lean`'s umbrella
`Mathlib` import and historical metadata. Deprecated conditional-rewrite
names are updated. The new direct subgroup proofs and the shortened
`ord_unitGroup` proof are internal derivations of the displayed definitions.
No uniformizer choices, conductor existence results, or finite local constant
are introduced.
