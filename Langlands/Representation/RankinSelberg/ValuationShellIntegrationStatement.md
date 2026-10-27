# Valuation-shell decomposition of normalized multiplicative Haar integrals

`Langlands.RankinSelberg.ValuationShellIntegrationStatement.{uF}` is a
Prop-valued definition. It states one change-of-variables and decomposition
result for the actual normalized multiplicative Haar measure on the unit group
of a p-adic field, and proves nothing. It is a derived internal interface for
the valuation-shell proof route of the unchanged
`Langlands.RankinSelberg.OneVariableMellinStatement`; it is not a separately
numbered result of the cited literature.

The sole new public declaration is the proposition itself. The measure, the
integral units, the shells and the uniformizer are local to it; no global shell
or uniformizer definition is introduced.

## Binders and local instances

The proposition quantifies over every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p` and every supplied `T : F.TopologicalData`. It installs
exactly the instances of `OneVariableMellinStatement`: `T.topology`,
`T.valuativeRel`, `T.localField`, the Borel measurable structure
`borel F.Carrier` with its `BorelSpace` witness, and `borel F.Carrierˣ` with its
`BorelSpace` witness. The unit group carries Mathlib's units topology induced by
`T.topology`. The field universe is arbitrary.

It then fixes three local definitions:

```text
μ   := localMultiplicativeHaar F.Carrier                    -- Measure F.Carrierˣ
K   := (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ)
S n := {a : F.Carrierˣ | T.ord (a : F.Carrier) = n}         -- n : ℤ
```

`μ` is the actual measure from `RankinSelberg.Measures`, normalized so that the
integral units have mass one (`localMultiplicativeHaar_integerUnits`). `K` is the
actual group of units of the valuation integer ring, viewed in the field's units.
`T.ord` is the normalized order of `LocalField.Normalization.Definitions`, whose
value on a unit is its genuine order since units are nonzero. No replacement
measure, alternate normalization or supplied decomposition appears.

The proposition asserts the existence of `π : F.Carrierˣ` with
`T.ord (π : F.Carrier) = 1` such that the four groups of conclusions below hold
for this one `π`. Here `π ^ n` is the integer power in the unit group.

## 1. Shell geometry

- `S 0 = K`: the order-zero units are exactly the integral units.
- `Pairwise (fun m n : ℤ => Disjoint (S m) (S n))`: distinct integer shells are
  disjoint.
- `(⋃ n : ℤ, S n) = Set.univ`: the shells cover the full unit group.
- For every `n : ℤ`:
  - `S n = (fun u : F.Carrierˣ => π ^ n * u) '' K`, so each shell is the left
    translate of the integral units by `π ^ n`;
  - `S n` is open, compact and measurable (`IsOpen`, `IsCompact`,
    `MeasurableSet`) in the units topology and its Borel structure;
  - `μ (S n) = 1`;
  - every `a ∈ S n` satisfies
    `T.normalizedAbs (a : F.Carrier) = (T.residueCardinality : ℝ) ^ (-n)`,
    where the right side is the integer power (`zpow`) of the real residue
    cardinality `q`. Thus `|a| = q^(-n)` on the `n`-th shell.

## 2. Local integrability

For every continuous `f : F.Carrierˣ → ℂ` and every `n : ℤ`, the translate
`u ↦ f (π ^ n * u)` is `IntegrableOn K μ`. This is a statement about each shell
separately; it implies no global integrability.

## 3. Global integrability criterion

For every continuous `f : F.Carrierˣ → ℂ`,

```text
Integrable f μ  ↔  Summable (fun n : ℤ => ∫ u in K, ‖f (π ^ n * u)‖ ∂μ).
```

The right side concerns the nonnegative real shell integrals of the norm, and
`Summable` is Mathlib's default unconditional summability over `ℤ`. No
summability hypothesis is added on either side; the equivalence characterizes
actual integrability over the whole unit group.

## 4. Actual integral identity

For every continuous `f : F.Carrierˣ → ℂ` with `Integrable f μ`, the scalar shell
integrals are summable and the actual Bochner integral decomposes:

```text
Summable (fun n : ℤ => ∫ u in K, f (π ^ n * u) ∂μ),
∫ a, f a ∂μ = ∑' n : ℤ, ∫ u in K, f (π ^ n * u) ∂μ.
```

Both sides use the actual measure `μ`; the sum is the unconditional `tsum`.

## Scope

The integration assertions are restricted to continuous complex-valued
functions. This is deliberate: it is intended for the scalar integrands
`Φ(a) η(a) |a|^(ms)` of the ordinary one-variable Mellin statement and of the
ramified scalar route, which are continuous on the unit group (a fact a
consumer must prove; it is not part of this proposition). The proposition
contains no growth estimate, recurrence, Mellin rationality, ramified
cancellation or principal-unit assertion; those belong to separate statements.

Every conclusion concerns the actual objects in the target: the shells are
defined through the actual normalized order, and the shell integrals are taken
against the actual measure restricted to the actual integral units.

## Original sources and derivation

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464, Theorem (2.7) (stated on printed pp. 390–391) and the
  proof of its parts (i)–(ii), printed pp. 391–392 (one-based PDF
  pp. 26–27), especially display (6) on p. 392 and the following
  convergence and rationality paragraphs. Registered source:
  `jpss-1983-rankin-selberg`; retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

Printed pp. 390–392 were read from rendered page images (the PDF has no text
layer). Neither the project nor the Library had an errata directory when
checked on 2026-10-27.

Display (6) is a product of one-variable integrals
`∫ Φ_i(a_i) η_i(a_i) |a_i^i|^s d^×a_i` over `F^×`. JPSS then assert, without
displaying the computation, that each such integral converges for large real
part and has the form `Q_i(X)(1 - α_i X)^(-k_i)` in `X = q^(-s)`. Proving that
assertion by summing over the sets of fixed valuation uses exactly the
decomposition stated here: `F^×` is the disjoint union of the shells
`π^n O^×`, the multiplicative measure gives each shell the mass of `O^×`, and an
integral over `F^×` is the sum of its shell integrals. This standard
change-of-variables step is not stated as a separate result in JPSS; the
proposition is formulated here as an internal interface for the parent proof
of `OneVariableMellinStatement`, and the restriction to continuous integrands,
the integrability criterion and the explicit normalizations are choices of
this formalization.

## Remaining proof obligation

A later exact-target proof must establish all four groups. Expected
ingredients are the order formulas of `LocalField.Normalization.Proof`
(`ord_uniformizer`, `ord_mul`, `ord_zpow`, `normalizedAbs_of_ne_zero`), the
nonvanishing of `T.uniformizer`, local constancy of the order on units, left
invariance of `μ` and `localMultiplicativeHaar_integerUnits`, and Mathlib's
countable disjoint-union integral lemmas. Compilation only checks that the
declaration is a well-formed proposition; it establishes none of the
mathematical assertions.
