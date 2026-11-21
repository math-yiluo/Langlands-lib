# The signed kernel-rank height of an atlas quasi-isogeny

`BasicAtlas.QuasiIsogeny.heightOnChart` measures the actual rational section of
the invertible tensor on a chart test. The original source and target charts
supply the scalar-height certificates, which extend to the coefficient test.
The affine tensor height theorem verifies the rank presentation and its
uniqueness.

`heightOnChart_natural` compares the two tested tensors using the coefficient
triangle isomorphisms of the source and target. Coefficient extension pulls
the rank function back on spectra. The two integral comparisons preserve that
pullback. On an overlap, the actual transition square gives a second integral
comparison, proving `heightOnChart_transition`.

`heightFunction` on the base spectrum chooses a principal chart containing a
prime and evaluates the chart height at the prime's lift to the localization.
`heightOnChart_eq_heightFunction` verifies that every test reads this function.
Its proof inverts the chosen chart generator in the test algebra and lifts the
test prime there. On that common test, coefficient naturality on both charts
and the transition comparison give the same value. The open embedding of a
principal chart and local constancy there prove local constancy on the base.
`hasConstantChartHeight_iff` identifies constant base height with the earlier
verified constant chart relation, including its zero fibre.

This construction supplies an actual rank-height function for coordinate
atlases in the split moduli comparison of Rapoport–Zink, (6.17) and Lemma 6.44,
printed pp. 309–310, and for the local rank height of rigidifiers in Harris
1997, Appendix, printed pp. 112–113.
