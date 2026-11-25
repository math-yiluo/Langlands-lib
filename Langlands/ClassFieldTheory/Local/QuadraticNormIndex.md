# The norm group of a quadratic extension of local fields

The module `Langlands.ClassFieldTheory.Local.QuadraticNormIndex` proves that the norms of a
quadratic Galois extension of nonarchimedean local fields form a subgroup of index two, and
defines the quadratic character attached to the extension.

## Content

Let `F` be a nonarchimedean local field (Mathlib's class `IsNonarchimedeanLocalField`, any
characteristic) and `E / F` a Galois extension of degree two. Local class field theory gives an
isomorphism `Fˣ / N_{E/F}(Eˣ) ≅ Gal(E/F)ᵃᵇ`, and `Gal(E/F)` has order two; hence:

- `index_range_norm_eq_two`: the subgroup `N_{E/F}(Eˣ)`, written
  `(Units.map (Algebra.norm F : E →* F)).range`, has index `2` in `Fˣ`.
- `mul_mem_range_norm_of_finrank_eq_two`: the product of two non-norms is a norm. This is the one
  statement of local class field theory that the Leray splitting of `U(ν, ν)` of the metaplectic cover over a
  unitary dual pair uses (through the multiplicativity of the quadratic character, which enters
  the Gauss integrals of `Langlands/Theta/DualPair/Unitary/`).

Both are read off from the local norm-residue symbol of the separate library NYLL,
`LocalClassFieldTheory.localArtinMonoidHom F E : Fˣ →* Abelianization Gal(E/F)`, which is surjective
(`localArtinMonoidHom_surjective`) with kernel NYLL's norm subgroup
(`localArtinMonoidHom_ker`); `range_unitsMap_norm_eq_localNormSubgroup` identifies that subgroup
with the range of the norm on units. The abelianization of a group of order two has order two.
NYLL's theorem is stated for fields in `Type`, so the statements here are too.

`normResidueSign F E : Fˣ →* ℤˣ`, for `[Algebra.IsQuadraticExtension F E] [IsGalois F E]`, is the
quadratic character `η_{E/F}` of `F` attached to `E`: `1` on norms, `-1` on non-norms
(`normResidueSign_of_mem`, `normResidueSign_of_notMem`, `normResidueSign_eq_one_iff`,
`normResidueSign_eq_neg_one_iff`, `normResidueSign_norm`). It is multiplicative by
`mul_mem_range_norm_of_finrank_eq_two`. In characteristic zero, Mathlib's instances give
`IsGalois F E` from `Algebra.IsQuadraticExtension F E`. `normResidueSign_pow_eq_ite` writes
`η(a)ⁿ ∈ ℂ` as `1` or `(-1)ⁿ`, the form in which the condition on the characters `χ` of Kudla's
splitting is stated (Harris–Kudla–Sweet, *Theta dichotomy for unitary groups*, J. AMS 9 (1996),
§1, (1.5), p. 951: `χ_V|_{Fˣ} = ε_{E/F}^m` with `m = dim_E V` and `ε_{E/F}` the quadratic character
of `E/F`).

The Library's own local reciprocity for its `PadicField` structures
(`Langlands/ClassFieldTheory/Local/FiniteReciprocityStatement.lean`) would give the same in
characteristic zero; NYLL's is used because it is stated for Mathlib's class
`IsNonarchimedeanLocalField`, which the files of `Langlands/Theta/DualPair/Unitary/` use.

## Source and licence

The statement of `mul_mem_range_norm_of_finrank_eq_two` and the definition of `normResidueSign`
replace `GlobalTheory.KSp.NormIndex.mul_mem_range_norm`
(`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulMemRangeNorm.lean`, lines 31–69),
`GlobalTheory.KSp.sgn` (`src/Development/AbelianVarietyTheory/Definitions/Divisors/UnipVal.lean`,
lines 50–51) and `GlobalTheory.KSp.sgn_mul_of_isQuad`
(`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalNormResidueSignMul.lean`) of
<https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`. The case analysis
in `normResidueSign` follows `sgn_mul_of_isQuad`, and the lemma on groups of order two follows
`mul_eq_one_of_card_two` (`MulMemRangeNorm.lean`, lines 15–29). The repository has no licence
file; the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- The source proves `mul_mem_range_norm` from its own local class field theory in characteristic
  zero (`ReciprocityTheory.DiscreteGroups.LocalClassField.artin_reciprocity_char_zero`, which
  reaches about 12,000 lines of class field theory and group cohomology); here it is proved from
  NYLL's `localArtinMonoidHom_ker`, in every characteristic, for a Galois extension of degree two
  (the source assumes `[CharZero F]` and a quadratic involution of `E`; the bridge from that
  hypothesis is in `Langlands/Group/Unitary/Basic.lean`).
- The source's function `sgn E : Fˣ → ℂ` with a separate multiplicativity lemma becomes the
  homomorphism `normResidueSign F E : Fˣ →* ℤˣ`.
- New: `index_range_norm_eq_two`, `range_unitsMap_norm_eq_localNormSubgroup`, the lemmas on
  `normResidueSign`.

## Declarations

- `range_unitsMap_norm_eq_localNormSubgroup`
- `mul_mem_range_norm_of_finrank_eq_two`
- `index_range_norm_eq_two`
- `normResidueSign`, `normResidueSign_of_mem`, `normResidueSign_of_notMem`,
  `normResidueSign_eq_one_iff`, `normResidueSign_eq_neg_one_iff`, `normResidueSign_norm`,
  `normResidueSign_pow_eq_ite`

All in the namespace `Langlands.LocalClassField`.

## Dependencies

NYLL: `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main`
(`localArtinMonoidHom`, `localArtinMonoidHom_ker`, `localArtinMonoidHom_surjective`; through it
`LocalFieldTheory.localNormSubgroup`, `normUnits`). Mathlib: `FieldTheory.Galois.Basic`.
