# General residue-normalized absolute value

For any universe `u`, this module uses an actual field `F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`.
There is no characteristic, p-adic-extension, or splitting restriction.
It reuses `Langlands.FML.ord : AddValuation F (WithTop ℤ)` and
`Langlands.FML.normalizedMultiplicativeValuation`, imported from
`Langlands.LocalFactor.FML.Valuation`. The existing order has the source's
sign convention and sends zero to infinity; this module introduces no
competing additive valuation. Its existing product, sum, comparison and
integer-ring laws remain available.

The added intrinsic API in `Langlands.FML` consists of:

- `normalizedMultiplicativeValuation_surjective`, the onto property of the
  existing multiplicative valuation;
- `ord_of_ne_zero`, the exact formula
  `ord F x = ((-WithZero.log (normalizedMultiplicativeValuation F x) : ℤ) : WithTop ℤ)`
  for `x ≠ 0`; at zero the existing `ord_zero` gives `⊤`;
- `ord_surjective_nonzero`, realizing each integer at a nonzero field element,
  and `ord_surjective`, realizing every value in `WithTop ℤ`;
- `mem_maximalIdeal_iff_ord_pos`, characterizing membership of an element of
  the actual valuation ring in its actual maximal ideal by positive order;
- `mem_unitGroup_iff_ord_eq_zero`, characterizing membership in the existing
  integral-unit subgroup of `Fˣ` by order zero.

In `Langlands.LocalField`, `ResidueField F` is the actual residue field
`IsLocalRing.ResidueField (Langlands.FML.ringOfIntegers F)`;
`residueCardinality F : ℕ` is its `Nat.card`. `finite_residueField` reuses the
finite-residue-field instance supplied by Mathlib's local-field interface,
and `residueCardinality_gt_one` proves `1 < residueCardinality F` from the
field's distinct zero and one. The noncomputable `uniformizer F : F` chooses
a nonzero element of order one by order surjectivity.
`uniformizer_ne_zero` and `ord_uniformizer` expose its certificates. This
choice need not be definitionally equal to another chosen uniformizer.

`residueNormalizedAbsoluteValue F : AbsoluteValue F ℝ` is the composition of
the existing normalized multiplicative valuation with Mathlib's
`WithZeroMulInt.toNNReal` at the actual residue cardinality, followed by
coercion to the reals. Its constructor proves multiplicativity,
nonnegativity, the zero criterion and the triangle inequality, so the
standard `AbsoluteValue` API supplies these laws and its values at zero and
one. No desired property is an additional hypothesis.
`residueNormalizedAbsoluteValue_add_le_max` supplies the stronger ultrametric
inequality. Writing `q = residueCardinality F`, the formula is

\[
|0|_F=0,\qquad |x|_F=q^{-n}\quad\text{when }\operatorname{ord}_F(x)=n\in\mathbb Z.
\]

The finite-order formula is `residueNormalizedAbsoluteValue_of_ord_eq`.
`residueNormalizedAbsoluteValue_of_ne_zero` also gives the formula directly
in multiplicative-valuation logarithm coordinates.
`residueNormalizedAbsoluteValue_uniformizer` evaluates the chosen
uniformizer as `q ^ (-1 : ℤ)`;
`residueNormalizedAbsoluteValue_of_ord_one` evaluates any order-one element
as `q⁻¹`; and `residueNormalizedAbsoluteValue_unit` evaluates every member of
`Langlands.FML.unitGroup F` as one.

The proofs of surjectivity use the surjectivity of the actual valuation and
Mathlib's ordered value-group isomorphism. The maximal-ideal and unit-group
proofs use the existing FML order comparisons and Mathlib's valuation-ring
unit criteria. The absolute-value construction uses the zero-preserving
multiplicative homomorphism `WithZeroMulInt.toNNReal`; its strict monotonicity
at `q > 1` carries the valuation's bound on sums to the ultrametric bound and
hence to the ordinary triangle inequality. Its nonzero evaluation and the
FML logarithm formula give the normalization statements.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French 9 July 2026 version, V.1, printed page 103 / PDF page 109:
the normalized surjective order, integer ring, maximal ideal, units,
uniformizer, finite residue field and normalized absolute value. Printed
page 104 / PDF page 110 provides the neighboring topology and Haar context.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These original pages were read, and PDF page 109 was visually checked.
The implementation and intrinsic API are derived from the existing Library
and Mathlib definitions; the proof route does not invoke the source's
unformalized reference [21]. Mathlib is the project's pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`; the main constructors are in
`Mathlib.NumberTheory.LocalField.Basic` and `Mathlib.Data.Int.WithZero`.

The registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF page 8, correction to the 2010 edition's printed page 120, line 11,
corrects the Haar factor to the inverse absolute value. That correction is
already present in the governing 2026 passage and changes none of this
unit's definitions. The 2010 errata are supplementary evidence, not a
replacement edition.

The supplied-data p-adic comparison is in
[PadicResidueNormalization](PadicResidueNormalization.md). This general
unit does not prove the source's unique unit-times-uniformizer-power
decomposition, topology and congruence-neighborhood assertions, Haar
formula, or algebraic-group assertions. Those remain separate obligations.
Worker 607 authored this construction and its intrinsic laws.
