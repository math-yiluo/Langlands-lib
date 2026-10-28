# Conditional unequal-rank source-carrier descent

This internal construction implements the elementary final descent
step for `UnequalRankBilinearUniquenessStatement`. It does not establish
the outstanding source-carrier length bound and is not a completed
proof of the parent theorem.

`coefficientModelBilinearPullback` constructs a complex linear map on
the full bilinear-form spaces by composition with the two actual
`Whittaker.modelMap` intertwiners, using `LinearMap.compl₁₂`.
The two maps are surjective by the image definition of the coefficient
models. Mathlib's `LinearMap.compl₁₂_inj` therefore gives injectivity of
pullback, recorded in `coefficientModelBilinearPullback_injective`,
including for specified zero functionals.
`coefficientModelBilinearPullback_covariant` uses the intertwining
equations to transport the determinant covariance through the actual
`unequalRankEmbedding` and the unipotent covariance through the actual
`unequalRankUnipotentLift`.
`coefficientModel_uniqueness_of_source` then proves that a nonzero model
form has nonzero pullback and that source-carrier scalar proportionality
descends by injectivity and linearity.

The private submodule helper turns module length at most one into scalar
proportionality to any nonzero element. Such an element excludes length
zero, so the module has length exactly one and is simple. Its nonzero
element spans it. This is the same elementary route as the public
same-group `InvariantBilinear.exists_smul_eq_of_length_le_one`.

`unequalRankBilinearUniqueness_of_source_length` preserves independent
field and carrier universes and has the exact parent proposition as its
conclusion. Its extra hypothesis is the still outstanding finite-exception
bound on the actual `unequalRankMirabolicForms` of the original first
representation restricted to its mirabolic group and the original second
representation of the smaller general linear group. That hypothesis
chooses the exceptional set before the parameter and even before the
specified model functionals. The proof obtains source proportionality
from that length bound and applies the preceding descent theorem.

This is internal algebraic assembly, with independent field and carrier
universes. The pullback construction requires only a topological field;
neither smoothness nor a nonzero assumption on either specified
functional is used. Its implementation follows the
source-carrier descent pattern in
`RankinSelberg.EqualRankTrilinearAssembly`, adapted to the two published
unequal-rank covariance laws and to bilinear forms. It does not invoke
JPSS's irreducible lemma, prove a mirabolic finite-length theorem, or
derive any pairwise rigidity. Those prerequisites and the mixed
functional-factor assembly remain necessary to discharge its explicit
length-bound input and prove the exact parent theorem without additional
hypotheses.
