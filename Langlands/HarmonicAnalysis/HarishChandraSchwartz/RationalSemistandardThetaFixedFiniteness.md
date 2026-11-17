# Full and proper VIII.1.3(i) with the required comparison exposed

This unit states the forward induced-fixed-vector comparison needed for
fixed-index finiteness, and proves conditional full/proper finiteness adapters.
It separately states the two-way comparison at projection-compatible normal
levels and the cofinal adapted-refinement property. The proper finiteness
adapter requires neither comparison nor local VIII.1.2 at a group index.

## Source and hypotheses

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), printed p.321, Remarque VIII.1.3(i), its
proper-Levi variant and following explanation; also I.5, printed p.246, for
the convention of compact open levels with
`H = (H intersect U)(H intersect M)(H intersect opposite U)`.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The interfaces and conditional proof route are derived from this argument.

The field, affine locally finite type actual-point ambient group, literal Levi
models, actual normalized inductions, split components and measures are exactly
those of `RationalSemistandardThetaFixed`. The field may have positive
characteristic, the group may be nonsplit or non-quasi-split, and relative rank
may be zero. Representation universe `uV` is independent of `u`.

Normality inside the chosen compact subgroup does not by itself identify
`projection(L intersect P)` with `M intersect L`. The converse implication
from Levi fixed vectors to induced fixed vectors therefore has an explicit
level condition below. The finiteness proof needs only the forward implication
and uses the ordinary normal-refinement theorem, without that extra condition.

## Targets and dependency ledger

Names are in `Langlands.HarishChandraSchwartz`.

| Declaration | Exact meaning and retained inputs | Status |
| --- | --- | --- |
| `RationalSemistandardLevelProjectionCompatible p L` | The actual subgroup image `(L.comap (parabolic p).subtype).map (decomposition p).projection` equals the literal `leviLevel p L`. | Explicit Prop-valued level condition; not inferred from normality. |
| `RationalSemistandardNormalLevelFixedComparisonAt p K` | For every compact open `L` contained and normal in `K` and every actual smooth representation `A` of the literal Levi, nonzero `(I_P^G A)^L` implies nonzero `A^(M intersect L)`. | Unproved substantive forward-comparison target. |
| `RationalSemistandardNormalLevelFixedComparison K`, `RationalProperSemistandardNormalLevelFixedComparison K` | The forward target at every index, or only at proper indices. | Distinct full/proper premises. |
| `rationalProperSemistandardNormalLevelFixedComparison_of_full` | Restricts the full forward premise to proper indices. | Elementary adapter. |
| `RationalSemistandardAdaptedNormalLevelFixedComparisonAt p K` | The same levels and representations, with `RationalSemistandardLevelProjectionCompatible p L` as an additional premise, conclude nonzero induced fixed vectors iff nonzero literal-Levi-intersection fixed vectors. | Unproved substantive equivalence target at adapted levels only. |
| `RationalSemistandardAdaptedNormalLevelFixedComparison K`, `RationalProperSemistandardAdaptedNormalLevelFixedComparison K` | The adapted equivalence at all indices, or only proper indices. | Separate full/proper targets, not premises of the finiteness adapters. |
| `rationalProperSemistandardAdaptedNormalLevelFixedComparison_of_full` | Restricts full adapted comparison to proper indices. | Elementary adapter. |
| `RationalSemistandardAdaptedNormalRefinementStatement K` | Each compact open `H` has a compact open refinement `L` below `H` and `K`, normal in `K`, and projection-compatible at every intrinsic index. | Separate unproved cofinality property of the specified `K`; not claimed for arbitrary `K` and not supplied by ordinary normal refinement. |
| `RationalSemistandardSpecialCompactFixedComparisonStatement nu K` | Under explicit connected reductivity, maximal split torus, generic cocharacter, published `SpecialCompactProperties F i nu K`, actual projection continuity and Iwasawa factorization at this same `K`, concludes both the full forward comparison and the adapted-level equivalence. | Unproved source-setting target. Its equivalence retains the level condition; it does not conclude adapted cofinality. |
| `inducedFixedOrbits_subset_leviFixed` | The one-index forward comparison sends each existential induced-fixed orbit into the actual Levi-intersection fixed-orbit set. | Conditional elementary inclusion. |
| `finite_semistandardInducedFixedOrbits_of_local` | That forward comparison, local VIII.1.2 for one actual Levi model, and the specified Borel/Haar quotient data imply finiteness of its induced-fixed orbit fiber. | Conditional elementary adapter. |
| `finite_rationalSemistandardThetaFixed` | Compactness of `K`, geometric `Finite (SemistandardSpectralIndex i)`, full forward comparison and all-Levi local VIII.1.2 imply finite full fixed indices at every compact open `H`. | Conditional full VIII.1.3(i) adapter. |
| `finite_rationalProperSemistandardThetaFixed` | The same compact and geometric inputs, but only proper-index forward comparison and proper-Levi local VIII.1.2, imply finiteness of the fixed set intersected with the proper part. | Conditional proper VIII.1.3(i) adapter. |
| `RationalSemistandardThetaFixedFinitenessStatement a ha mu K`, `RationalProperSemistandardThetaFixedFinitenessStatement a ha mu K` | Exact corresponding implications, with Borel quotient structures, compactness of `K`, geometric index finiteness and the respective forward/local premises explicit. | Prop targets discharged by `rationalSemistandardThetaFixedFiniteness` and `rationalProperSemistandardThetaFixedFiniteness`. |

The fixed and proper sets use the imported full index and actual orbit relation.
Geometric index finiteness is a displayed premise, distinct from VIII.1.2; the
adapters prove no `SemistandardSpectralFinitenessStatement`. Its existing
geometric target can later supply this premise for the source group and torus.
Borel quotient structures occur as logical premises in the two proposition
targets and as typeclass parameters in the pointwise adapters. Split components
and quotient Haar measures remain the family's actual parameters.

The level condition uses the actual Levi projection of the published
semidirect decomposition, not an abstract projection or a supplied equivalence.
For an approach using the adapted equivalence at refinements, cofinality of such
levels is an additional substantive obligation. No theorem here derives it from
normality or the properties of `K`, and no compact datum stores it. The route
implemented here avoids that obligation by consuming only forward comparison
at ordinary normal refinements. All source-setting targets retain actual
projection continuity and Iwasawa factorization; no special maximal compact is
constructed here.

## Implemented conditional proof

At a compact open normal level, unfold the existential induced-fixed orbit
membership. For its witnessing discrete-series class, quotient induction lets
the one-index forward comparison transfer a nonzero induced fixed vector to a
nonzero vector fixed by the literal intersection. The same class witnesses
membership in the Levi fixed-orbit set. Local VIII.1.2 transfers from the actual
Levi scheme by `finite_fixedOrbits_of_local`; openness and compactness of the
intersection were proved in the companion. Finite containment proves the
induced-fixed orbit fiber finite. The converse comparison is never used.

Geometric finiteness of the intrinsic index then gives a finite sigma union.
The proper version takes only proper indices and invokes local finiteness and
forward comparison only after obtaining `p.IsProper`. This union is exactly the
full fixed set intersected with the proper set; no application at `P = G` occurs.

Finally `compactOpenNormalRefinement` supplies an ordinary normal compact open
refinement below the given `H`. Fixed-index antitonicity includes the original
fixed set in the refined finite set. `finite_of_compactOpenNormalRefinement`
packages that step. The forward comparison, the adapted equivalence, adapted
cofinal refinement, analytic VIII.1.2, arbitrary-level orbit independence and
all Fourier conclusions remain separate substantive obligations. The two
conditional finiteness theorems prove only their displayed implications.
