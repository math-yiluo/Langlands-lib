# Truncations of the standard integral and Casselman compression

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It works with
the existing general standard integral of `StandardIntertwiningIntegral`. The
data are a nonarchimedean locally compact group `G`, an actual semidirect
decomposition `P = M ⋉ U` with closed `U`, a second subgroup `U'`, and a
smooth complex representation `A` of `M`. It integrates the actual integrand
`integrand h hU U' A g f` over subsets of the radical quotient
`(U ∩ U') \ U'` and proves the following.

1. A Levi element shifts the truncation set by the published quotient
   conjugation.
2. Target-radical translations preserve stable truncations.
3. Monotone exhausting truncations converge to the full selected integral.
4. Under an explicit Iwahori contraction, iterated Casselman compression by a
   contracting element realizes exactly these shifted truncations.

The final theorem `tendsto_compressedTruncation` gives the weak convergence
used by the regular stable-limit principle of `UnramifiedStableLimit`. The
module does not choose or construct the compact subgroup, the contracting
element or the Iwahori factorization. It does not prove full convergence,
polynomial dependence on an unramified parameter, or any rationality
statement.

## Truncated integrals

`truncatedIntegral h hU U' A ν C g f ℓ` is the complex set integral over `C`
of `ℓ(integrand h hU U' A g f q)` against the supplied quotient measure `ν`,
for a smooth functional `ℓ`. No measurability or integrability is part of the
definition.

- `integrable_scalar_of_mem_domain`: for `f` in the published `domain`, every
  scalar test of every integrand is integrable. This is the first component
  of `HasIntegral`.
- `truncatedFunctional C g ℓ` is truncation as a complex linear map on the
  actual domain. Additivity uses this integrability. Homogeneity is
  `integral_const_mul`.
- `truncatedIntegral_smul_functional`: truncation is homogeneous in the
  functional.
- `tendsto_truncatedIntegral`: for measurable sets `C n`, monotone in `n`, with
  union the whole quotient, the truncations of a domain vector converge to
  `ℓ(operator … f g)`. The proof combines Mathlib's
  `tendsto_setIntegral_of_monotone` with the published `operator_eval`.

## Radical translations and Levi shifts

Assume the published compatibility
`QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν`.

`truncatedIntegral_unipotent`: let `u ∈ U'`, and suppose `C` equals its
preimage under the quotient right translation by `u`. Then the truncation of
the translated vector `R(u) f`, evaluated at `1`, equals that of `f`. By the
published `integrand_right_action` and `integrand_unipotent_mul`, the
integrand of `R(u) f` is the integrand of `f` composed with right translation.
The compatibility field `right_invariant` makes this translation
measure-preserving, and `MeasurePreserving.setIntegral_preimage_emb` finishes
the proof.

`leviShiftFactor m` is the published actual Levi factor: the positive
half-character `HaarModulus.closedHalfCharacter U hU M …` at `m`, times the
published `quotientConjugationModulus` at `m`. Thus it is the same factor that
appears in the published `operator_levi_mul`.

`truncatedIntegral_levi`: for `m ∈ M` with `M` normalizing `U'`, and measurable
`C`,

`truncatedIntegral C 1 (R(m) f) ℓ = leviShiftFactor m *
truncatedIntegral (φₘ ⁻¹' C) 1 f (ℓ ∘ A(m))`,

where `φₘ = quotientConjugation h U' hMU' m`, and the functional is the smooth
contragredient of `m⁻¹`, which evaluates as `w ↦ ℓ(A(m) w)`. By
`integrand_right_action` and `integrand_levi_mul`, the integrand of `R(m) f`
at `q` is the half-character times `A(m)` applied to the integrand of `f` at
`φₘ⁻¹ q`. Next, the indicator of `C` at `q` is the indicator of `φₘ ⁻¹' C` at
`φₘ⁻¹ q`. The published change of variables `integral_quotientConjugation_symm`
then gives the conjugation modulus.

## Compression on fixed vectors

Assume moreover that `domain h hU U' A ν` is the whole source and that the
induced representation is smooth (`hρ`). `truncatedLinear` is truncation
composed with the identification of the domain with the whole source, so it is
linear on all source vectors.

For an open compact subgroup `H`, a subgroup `O` and an element `a`, the
hypothesis is the published `Jacquet.IsIwahoriContraction H U' M O a`. It
gives an Iwahori factorization of `H` as `(H ∩ O)(H ∩ M)(H ∩ U')`,
conjugation conditions, exhaustion of `U'` and uniform contraction of `H ∩ O`.
`contractionLevi` is `a` as an element of `M`. A truncation set is
`IsRadicalStable` if it equals its preimage under right translation by every
element of `H ∩ U'`.

- `quotientConjugation_rightTranslate`: quotient conjugation by `m` intertwines
  right translation by `u` with right translation by `m u m⁻¹`. The proof
  checks representatives, using that `normalizerConj` is multiplicative.
- `isRadicalStable_preimage`: the preimage of a radical-stable set under
  quotient conjugation by the contracting element is radical-stable, because
  conjugation by `a` maps `H ∩ U'` into itself (field `upper`).
- `truncatedIntegral_compressedAction`: for `v` fixed by `H` and radical-stable
  `C`, the truncation of the published `Jacquet.compressedAction … H hH a v`
  equals that of `R(a) v`. The compression is the published compact average
  of `R(a) v`. The published `Jacquet.exists_upper_translate` writes every
  `H`-translate of `R(a) v` as an `(H ∩ U')`-translate. The radical
  invariance above and `Jacquet.map_averageMap_of_forall_eq` then evaluate the
  linear truncation of the average.
- `truncatedIntegral_compressedAction_pow`: by induction on `n`, for
  measurable radical-stable `C`, the truncation over `C` of the `n`-th power of
  the compression applied to `v` is `leviShiftFactor(a)^n` times the
  truncation of `v` over the `n`-fold iterated preimage of `C`, with functional
  the `n`-th power of the contragredient of `a⁻¹` applied to `ℓ`. Each step
  applies the compression identity to the fixed vector `Tⁿ v`, then the Levi
  shift with `m = a`, and the induction hypothesis to the stable measurable
  preimage. Multiplicativity of the Levi factor is never used.

## Exhaustion and convergence

`compactRadicalPiece U' H` is the image of `H ∩ U'` in the radical quotient.
It is open, by the published open quotient map
`QuotientIntegration.leftQuotient_isOpenQuotientMap`, and radical-stable. It
is contained in its preimage under quotient conjugation by `a`
(`compactRadicalPiece_subset_preimage`). The sets
`compactRadicalExhaustion n` are its `n`-fold iterated preimages. They equal
the preimages under the `n`-th iterate (`compactRadicalExhaustion_eq`), and
they are monotone (`monotone_compactRadicalExhaustion`). Their union is the
whole quotient (`iUnion_compactRadicalExhaustion`). For the union, the field
`exhaust` gives `r` with `aʳ x a⁻ʳ ∈ H`, and
`quotientConjugation_iterate_mk` identifies the `r`-th iterate on the class of
`x` with that representative.

`leviShiftFactor_ne_zero` holds because the half-character takes unit values
and the conjugation modulus is positive (`quotientConjugationModulus_pos`).
`dualCompressionShift` is the endomorphism of the smooth dual given by the
inverse Levi factor times the contragredient action of the contracting
element.

`truncatedIntegral_compressedAction_pow_dualShift`: the truncation over
`compactRadicalPiece U' H` of `Tⁿ v`, paired with `Sⁿ ℓ` for
`S = dualCompressionShift`, equals the truncation of `v` over
`compactRadicalExhaustion n` paired with `ℓ`. Indeed, `Sⁿ` is the scalar
`leviShiftFactor(a)⁻ⁿ` times the contragredient of `aⁿ`. Composing with the
contragredient of `a⁻ⁿ` leaves only the scalar, which cancels `leviShiftFactor(a)ⁿ`.

`tendsto_compressedTruncation`: for every `H`-fixed vector `v` and every smooth
functional `ℓ`, these paired truncations tend to `ℓ` of the selected integral
at `1`. This is the preceding identity followed by `tendsto_truncatedIntegral`
for the monotone exhausting measurable sets.

## Scope and provenance

All group, measure and representation inputs are explicit hypotheses or
published constructions. The intended application takes `H` with an Iwahori
factorization relative to the opposite of the target parabolic, and `a` a
Levi-central contracting point. The published opposite Iwahori basis results
supply such data for dynamic subgroups. Producing these data for the host's
supplied radicals, identifying the compression with a polynomial family on a
finite-dimensional compact-picture space, and the resulting uniform regular
denominator remain separate obligations.

The argument is internal. The compression lemmas it uses are the published
`Jacquet` results `compressedAction`, `exists_upper_translate` and
`map_averageMap_of_forall_eq`; their own Markdown records their source
conditions. Every step here is proved from the published Library declarations
named above, and no literature theorem replaces a proof. Waldspurger 2003, IV.1, printed
pp.280–282, obtains rationality instead from a Jacquet-module filtration,
which this module does not use.
