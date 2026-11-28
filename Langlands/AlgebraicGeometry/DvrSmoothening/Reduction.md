# Smoothenings from the affine lemmas on the defect of smoothness

- `isIso_pullback_snd_of_range_subset`, `isIso_pullback_map_of_range_subset`: the base change of a
  morphism `g` which is an isomorphism over an open `W` along a morphism with image in `W` is an
  isomorphism; in particular, if `W` contains the image of the generic fibre, `g` induces an
  isomorphism of generic fibres.
- `smooth_smoothLocus_ι`: the restriction of a morphism locally of finite presentation to its
  smooth locus is smooth.
- `isLocalization_away_of_irreducible`, `specMap_algebraMap_fraction_apply`: the fraction field of
  a discrete valuation ring is its localization away from a uniformizer.
- `genericallySmooth_of_smooth_pullback`: a smooth generic fibre gives `GenericallySmooth`.
- `exists_defect_bound`: for a quasi-compact scheme locally of finite type with smooth generic
  fibre, the defects of all test points are bounded (finite affine cover and
  `DefectBoundStatement`).
- `dvrSmoothening_of`: `DvrSmootheningStatement` follows from `DefectZeroSmoothAtStatement`,
  `DilatationDefectStatement`, `GoodChartStatement`, `DefectBoundStatement` and
  `BlowupChartStatement`, by `Induction.claim` applied to the family of all test points.

This is the deduction of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.1, Theorem 3 (printed
p. 61) from the results of §3.3 (printed pp. 64–71) through the induction of §3.4 (printed
pp. 71–73), in the form of §3.6, Lemma 5 (printed p. 79) for points of ramification index one.
