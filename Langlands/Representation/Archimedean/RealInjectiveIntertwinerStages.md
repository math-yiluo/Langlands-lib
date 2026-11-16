# Induction in stages of injective real standard intertwiners

This is an internal consequence of the published `RealInductionStagesInduce`,
`RealInductionStagesDerivative`, and `RealInductionStagesFiltration` modules. It adds no
representation theoretic hypothesis and makes no additional literature claim.

All function spaces and maps are the Library's concrete real standard module models.
`InductionStages.KFin n ds` denotes their orthogonal group finite functions. The main
theorem, `RealInjectiveIntertwinerExists.in_stages`, says that an injective standard
intertwiner between two lists `ds` and `es` of the same rank `r` extends to an injective
standard intertwiner between `pre ++ ds ++ post` and `pre ++ es ++ post`, provided the
first extended list has rank `n`.

The construction `InductionStages.standardInd` accepts a linear map and its
`IsRealStandardIntertwiner` proof and returns the induced linear map on the extended lists.
It rewrites `IsRealStandardIntertwiner` as commutation with the published operators `kRep`
and `lie`, then uses the induced map `InductionStages.ind`.
Compact equivariance is already `ind_kRep`. For Lie equivariance, the published
`sliceK_ind_lie_sub_mem` is applied to the zero submodule: exact equivariance on the middle
list makes every slice of the derivative defect zero. The detection theorem
`eq_zero_of_sliceK` then makes the defect itself zero. Injectivity follows from the slice
identity `sliceK_ind`, injectivity on the middle list, and the same detection theorem.

The auxiliary declarations are `InductionStages.isRealStandardIntertwiner_iff`,
`InductionStages.ind_lie`, `InductionStages.ind_isRealStandardIntertwiner`, and
`InductionStages.injective_ind`. The theorems `standardInd_intertwiner` and
`standardInd_injective` record the corresponding properties of `standardInd`.
This module supplies transport through surrounding lists;
it does not construct an intertwiner for any particular pair of middle lists.
