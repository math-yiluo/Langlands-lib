# Proof that power maps have non-open image on function-field adelic units

Author: Worker 1518.

`curvePlacePowerImage` proves `CurvePlacePowerImageStatement`: for every finite
field `k`, every function field `F` over `k` (with the compatible `RatFunc k`-algebra
structure) and every `n ≥ 2` with `¬ ringChar k ∣ n`, the image of `x ↦ x ^ n` is
not open in `(CurvePlaceAdeleRing k F)ˣ`, and for every base ring `R` the image of
composition with the actual power morphism `affineLinePuncturePow R n` is not open on
punctured-line points. Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.11, asserts the result for global fields
without an argument. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This proof is an independent derivation of the function-field case. It follows the
published number-field proof `numberFieldPowerImage`
(`Langlands/Global/NumberFieldPowerImageProof.lean`) and reuses its general lemmas;
only the supply of infinitely many suitable places is new. The route is the one
suggested in the task, except that it uses residue degrees divisible by `ℓ - 1`
instead of by the order of `|k|` modulo `ℓ`.

## Finite-field facts

`finiteField_exists_irreducible_natDegree`: over a finite field `k` there is an
irreducible polynomial of every degree `d ≠ 0`. Let `p` be the characteristic
(`CharP.exists`). Mathlib's `FiniteField.Extension k p d` has dimension `d` over `k`
(`FiniteField.finrank_extension`). Since `k` is perfect, it has a power basis
(`Field.powerBasisOfFiniteOfSeparable`). The minimal polynomial of its generator is
irreducible (`minpoly.irreducible`) of degree `d` (`PowerBasis.natDegree_minpoly`).

`prime_dvd_card_pow_mul_sub_one`: if `ℓ` is a prime different from `ringChar k`,
then `ℓ ∣ |k| ^ ((ℓ - 1) * j) - 1` for every `j`. Here `|k|` is a power of the
characteristic (`FiniteField.card`), so it is coprime to `ℓ`. Euler's theorem
(`Nat.ModEq.pow_totient`, with `φ(ℓ) = ℓ - 1`) gives `|k| ^ (ℓ - 1) ≡ 1 (mod ℓ)`;
raise it to the `j`th power.

`ratFuncPlace_natCard_residueField`: for an irreducible `f : k[X]`, the residue field
of the published rational-function-field place `RationalFunctionField.finitePlace k hf`
has `|k| ^ deg f` elements. The published `RationalFunctionField.deg_finitePlace`
says its dimension over `k` is `deg f`, which is positive, so it is finite over `k`
and `Module.natCard_eq_pow_finrank` applies. This lemma does not use finiteness of
`k`.

## Residue maps to an extended place

For a place `p` of `RatFunc k`, the published `curvePlaceExtension p` is a chosen
actual place of `F` whose valuation ring contains the image of that of `p`
(`curvePlaceExtension_mem`), and which sends the maximal ideal of `p` into its
nonunits (`curvePlaceExtension_dominates`).
`curvePlaceExtensionIntegersMap p` is the resulting ring map of valuation rings, and
`curvePlaceExtensionResidueMap p` is the induced map (`Ideal.quotientMap`) from the
residue field of `p` to the quotient of the upper valuation ring by its height-one
prime.

`curvePlace_finite_residue`: for every actual place `v` of `F`, the quotient of
`v.toValuationSubring` by `v.heightOneSpectrum.asIdeal` (the residue field) is
finite. The published `functionFieldPlaceResidue` shows that it is finite over `k`,
and `k` is finite (`Module.finite_of_finite`).

## Infinitely many good places

`exists_curvePlace_embedding_card_modEq_one`: for a prime `ℓ ≠ ringChar k` there is
an injective sequence `e : ℕ ↪ Place k F` such that `ℓ` divides the residue
cardinality of `e m` minus one, for every `m`.

For each `j`, choose an irreducible `f_j : k[X]` of degree `(ℓ - 1) * (j + 1)`, let
`p_j` be the place `RationalFunctionField.finitePlace k (hf j)` of `RatFunc k`, and
let `e j = curvePlaceExtension p_j`.

- Injectivity. The published `curvePlaceExtension_comap` recovers the valuation ring
  of `p_j` as the preimage of that of `e j`. So `e i = e j` gives `p_i = p_j`
  (`Place.ext`). Comparing degrees (`deg_finitePlace`) gives
  `(ℓ - 1) * (i + 1) = (ℓ - 1) * (j + 1)`, so `i = j`.
- Divisibility. The residue field of `p_j` has `|k| ^ ((ℓ - 1) * (j + 1))` elements,
  so `ℓ` divides its cardinality minus one by `prime_dvd_card_pow_mul_sub_one`. The
  residue map to `e j` is a ring map out of a field, hence injective, and so is the
  induced map of unit groups. By Lagrange (`Subgroup.card_dvd_of_injective`) and
  `Nat.card_units`, the lower residue cardinality minus one divides the upper one
  minus one, and divisibility by `ℓ` follows.

## Assembly

`curvePlace_units_powerImage_not_open` follows `numberField_units_powerImage_not_open`.
Choose a prime `ℓ ∣ n` (`Nat.exists_prime_and_dvd`); `ℓ ≠ ringChar k` since
`ringChar k ∤ n`. Take the sequence `e` above. For each place `v` in its range, the
published `exists_not_pow_mod`, applied to `B = v.toValuationSubring` and
`P = v.heightOneSpectrum.asIdeal`, gives `c_v` with `a ^ n - c_v ∉ P` for all `a`;
the case `a = 0` shows `c_v ∉ P`. At the other places, `c_v = 1`. The image of `c_v`
in the completion `curvePlaceCompletion v` has valuation `1`
(`valuedAdicCompletion_eq_valuation'`, `intValuation_eq_one_iff_mem_primeCompl`), so
it and its inverse lie in `curvePlaceCompletionIntegers v`.

The published `restrictedUnitAtPlace` puts this value at the single place `e m` and
`1` elsewhere. These units tend to `1` by the published
`tendsto_restrictedUnitAtPlace_val`. Their inverses are the one-place units of the
inverse values (`restrictedUnitAtPlace_inv_val`), which also tend to `1`. So the
units tend to `1` (`units_tendsto_one`). If the `m`th unit were `y ^ n`, its
coordinate at `e m` would be an `n`th power in the completion
(`restrictedUnitAtPlace_val_apply`, `RestrictedProduct.pow_apply`). This contradicts
the published `not_pow_in_adicCompletion`, applied to the Dedekind domain
`v.toValuationSubring` with fraction field `F`. Hence the power image is not open
(`not_isOpen_range_pow_of_tendsto`).

## Punctured-line points

`curvePlacePowerImage` proves both clauses, in arbitrary universe `u`. The first is
`curvePlace_units_powerImage_not_open`. For every base ring `R`, the published
`schemePoints_powerImage_not_open` transfers it to the image of
`affineLinePuncturePow R n` on actual punctured-line points of
`CurvePlaceAdeleRing k F`.
