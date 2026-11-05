# Rational fixed-order support from two structural prerequisites

`RationalCorrectedSupportPrerequisites` is the conjunction of the existing
uniform `GroupScheme.StandardParabolicPointsStatement.{u}` and
`BruhatTits.DynamicParabolicQuotientCompactStatement.{u}`. It records two
inputs to this internal reduction and proves neither. The existing
`RationalCorrectedSurvivingSupportStatement` and all its premises are
preserved.

The theorem
`rationalCorrectedSurvivingSupportStatement_of_prerequisites`
derives the whole unapplied rational proposition at field universe `u`
from this conjunction. Its proof introduces every binder of the
published target and installs the same affine, monomorphism, canonical
point-topology, finite simple-root and decidable Weyl-quotient instances.
It does not restrict the characteristic, splitness or quasi-splitness
of the connected reductive group and imposes no nonempty-root condition.
There is no representation-carrier universe.

The dependencies that supply the generic support theorem are:

| Required input | Exact deduction |
| --- | --- |
| Monotonicity of actual `parabolic i ν` | `standardParabolic_monotone` from the target's original `hOrder` |
| Closedness of every actual standard parabolic | `isClosed_standard_parabolic` from the target's original `hStandard` |
| Compactness of `Induction.LeftQuotient (parabolic i ν ∅)` | `compactSpace_leftQuotient_parabolic` from the additional uniform dynamic compactness input and the original standard-cocharacter, reductive, maximal-split and generic-cocharacter premises |
| Base/base actual normalizer-cell cover | `isBruhatCover_of_standardParabolicPoints` at the empty finite root set, from the additional points input |
| All actual parabolic-pair double-coset comparisons | `parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints`, from the points input and the target's original normalizer, full-centralizer and Levi-Weyl comparisons |

The proof then applies
`CorrectedFiltration.survivingSupportTarget_of_parabolicComparisons`
from `CorrectedSupportBoundary`. That theorem derives index separation
and strict boundary length decrease, and supplies both consecutive open
supports, left invariance and the exact single surviving double-coset
difference. It uses the literal decreasing-length list, including its
tie choices, the largest two-sided cores, and the original inverse-lift
convention. No new ordering or boundary premise is needed.

Some original target premises do not enter this proof route: the Levi
intersection statement, root-length comparison, positive-simple
reflection comparison, and the three unipotent/Levi topology premises.
They remain binders of the theorem's conclusion and are not removed from
the target.

The provenance is internal assembly from the named existing interfaces,
the rational comparison construction, and the proved closed-word
boundary argument. This is a conditional supporting result. Neither
uniform prerequisite is asserted or proved here, so this module is not an
unconditional proof or completion evidence for the assigned rational
target. Its proof becomes unconditional only after both actual structural
prerequisites have been proved.
