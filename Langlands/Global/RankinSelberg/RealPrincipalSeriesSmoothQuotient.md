# Continuous ascending quotients of real standard modules

`Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach.RealPrincipalSeriesSmoothQuotientStatement`
constructs a continuous full-group intertwiner from the genuine smooth
standard module of `ascendingExpand ds` to that of `ds`. Every compact-finite
vector of the target has a compact-finite preimage.

For a nonzero-weight induced block, the proof extends its ascending Fourier
tail map using the polynomial growth bound for the binomial symbol. The
extended map intertwines the full group by the compact and Lie identities,
and the algebraic tail surjection provides each compact-finite preimage.
For a zero-weight block the two underlying standard function spaces agree.
Their smooth identification preserves the compact profiles of every derivative
and the right translation of every function. `SmoothStandardQuotient.exists_preserving_function_of_eq` gives the pointwise identity of the reconstructed scalar functions, along with equivariance and the compact-finite preimages. List induction composes the maps.

The companion `exists_whittakerEvaluation_ascendingExpand` pulls back a given
continuous Whittaker evaluation by composing it with this intertwiner. It
preserves the unipotent character and realizes each original coefficient on
an actual compact-finite vector of the ascending smooth character model.

This is an internal consequence of the Library's block-intertwiner formulas
and its genuine smooth real standard models. It supplies the continuous
coefficient transfer used in the real Rankin–Selberg reduction.
