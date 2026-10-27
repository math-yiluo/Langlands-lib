# Conditional universal block-zero gamma assembly

Worker 112.

This derived interface packages the three universal inputs still required by
the block-zero gamma proof and proves that they imply the unchanged published
`UnequalRankBlockZeroGammaExistenceStatement`. Its inputs remain explicit.
It does not prove the universal analytic, continued-forms, full uniqueness or
unconditional gamma existence statements.

## Input proposition

`UnequalRankBlockZeroGammaAssemblyInput F T n r` uses any prime parameter,
`F : PadicField` in universe uF, supplied `T : F.TopologicalData`, and natural
numbers n,r. The two representation-carrier universes uV and uW remain
independent of each other and uF. The definition is the conjunction of:

- `UnequalRankAnalyticStatement F T n j k` for every j,k;
- `UnequalRankBlockZeroContinuedFormsStatement F T n r`;
- `UnequalRankBilinearUniquenessStatement F T n r`.

These are precisely the existing Library propositions. Packaging them asserts
none of them. The analytic premise is supplied for every block so it can be
used at the two complementary blocks; this assembly uses only (0,r-n-1) and
(r-n-1,0). The full Whittaker-type uniqueness premise includes reducible
representations. Its extension beyond irreducible generic representations is
still an input obligation.

## Implemented assembly

`UnequalRankBlockZeroGammaAssemblyInput.gammaExistence` consumes a proof of
the input proposition and proves
`UnequalRankBlockZeroGammaExistenceStatement F T n r`.

The proof unfolds the exact target, retaining the supplied topology and its
induced measurable and additive structures. It introduces its rank inequality,
unitary character, right-invariance instance, compatible quotient measure,
self-dual additive Haar measure, independent complex modules, Whittaker-type
representations and specified nonzero functionals.

The first inverse-transpose representation has Whittaker type for the
standard character of psi.scale(-1). This follows from the published
`isOfWhittakerType_inverseTransposePullback` and
`standardCharacter_scale_neg_one`. The second has inverse-standard type for
that same scaled character, by
`isOfWhittakerType_inverseTransposePullback_inverse` and
`inverseStandardCharacter_scale_neg_one`. These transports use the actual
inverse-transpose representations, without a smooth-contragredient
identification or an irreducibility hypothesis.

Two local specialization arguments take arbitrary j,k and an equality
r=n+(j+k+1). Substitution of that natural-number equality exposes the exact
`UnequalRankAnalyticConclusion` expected by `UnequalRankAnalyticAt`. Applying
the supplied analytic statement gives the original input. Applying the same
statement to psi.scale(-1), the inverse-transpose representations and the
actual dual functionals gives the dual input. The published
`firstDualFunctional_ne_zero` and `secondDualFunctional_ne_zero` discharge
their nonzero-functional requirements.

The proof now specializes these arguments to (0,r-n-1) and (r-n-1,0).
Both use the same supplied quotient measure mu and scalar Haar measure nu.
The rectangular measures are exactly `rectangularMeasure nu 0 (n+1)` and
`rectangularMeasure nu (r-n-1) (n+1)`. The continued-forms input is applied to
the original data and these two analytic conclusions. The uniqueness input
is applied to the original data to obtain its exact fixed-data conclusion.
Finally, `exists_blockZeroGammaEquation_of_analytic` applies with
`T.residueCardinality_gt_one`.

The result therefore retains a single nonzero rational G chosen before all
coefficient vectors, the actual complementary dual integral with
`blockWeylAt` right translation, inverse character and inverse-transpose
models, the derived model-minus-one scalar, a nonzero original rational
value, exponent r and all three denominator conditions. These are inherited
from the exact target and the published fixed-data adapter.
The self-duality hypothesis is retained by the target, although the
conditional assembly itself does not use it.

## Provenance and limits

This module is internal derived content from the published analytic,
continued-forms and uniqueness proposition definitions, actual dual
Whittaker-type transports, dual-functional nonvanishing and analytic
extraction adapter. It adds no new claim from original literature.
It changes no imported Lean/Markdown pair.

The conditional theorem supplies the universal specialization and assembly.
To prove the task's unconditional target, the three input propositions still
need actual published proofs. An independently accepted definition of this
interface does not discharge those mathematical obligations.
