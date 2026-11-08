# Compact invariance of the determinant-band form

Module: `Langlands.Automorphic.CuspidalUnitaryCompactForm`. Author: Worker 1827.

The Library constructs a positive definite Hermitian form on the original finite adelic
action of an operator realization with a unitary central character
(`OperatorDeterminantSlice.finiteInvariantPositiveForm`). The form is the `L²` pairing on the
determinant band of the rational quotient. This module proves that the same form is also
invariant under the standard infinite compact action, and packages the result for cuspidal
realizations.

## Results

* `OperatorDeterminantSlice.toQuotient_compact`: the quotient function of
  `S.compactRepresentation k f` is the quotient function of `f` composed with positive
  right translation by `AdelicGL.ofInfinite F n k.val`. It is proved pointwise from the
  Library's `OperatorRealization.evaluate_compactRepresentation`, exactly as the
  existing `toQuotient_finite`.
* `OperatorDeterminantSlice.inner_toL2_compact`: under the same hypotheses as the
  Library's `inner_toL2_finite`, the band `L²` inner product is invariant under the compact
  action. The proof copies the finite argument. `exists_normalized_rightTranslate` gives
  an idele `z` such that `a = scalar z * ofInfinite k` has determinant norm one, so right
  translation by `a` preserves the band measure (`measurePreserving_translate_band`). The
  central character turns the scalar into a phase of norm one, which cancels
  (`inner_phase`). The change of variables `MeasurePreserving.integral_comp` finishes.
* `CuspidalOperatorRealization.exists_compactInvariantForm`: if
  `HasUnitaryCentralCharacter T`, there is `b : InvariantPositiveForm T.realization.finiteRepresentation`
  with `b.inner (κ k f) (κ k g) = b.inner f g` for the compact action `κ`. The proof follows
  the Library proof `cuspidalUnitaryLocalUnitarity`. It unpacks the unitary character,
  uses the Borel structure on `AdelicGL F (r+1)` and the cover from
  `OperatorRealization.exists_band_cover` with band `[1,2]`, and obtains band square
  integrability from `memLp_band_of_cover`. It takes
  `b := finiteInvariantPositiveFormOfHaar ...`, whose inner product is definitionally the
  band `L²` inner product. Compact invariance is `inner_toL2_compact` with the Library's
  `measurePreserving_translate` (right invariance of the actual quotient Haar measure for every
  adelic matrix).

## Provenance

Internal and derived. The construction reuses the published band form and cover without
change; the only new mathematics is the compact-translation analogue of the existing
finite-translation invariance proof. It asserts no infinitesimal (Lie algebra) skewness of
the form.
