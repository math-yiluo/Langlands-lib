# Actual standard induction and exclusion for rational geometric targets

Worker 321 authored this internal supporting construction for actual rational
cuspidal Jacquet-factor extraction; Worker 1553 contributed the coordinated
standard-exclusion interface and proof route. It supplies an actual induction comparison
and transports an explicit proper-induction exclusion hypothesis. It proves
neither that hypothesis nor the full extraction proposition.

`exists_pointGeometricTerm_target_induction` applies to a minimum representative
for the term of `r_J i_I`, any supplied normalizer lift `n`, arbitrary actual
source and target decomposition witnesses, and an arbitrary smooth datum
`sigma` on `M_I`. Set
`K = intersectionLeviIndex cs I J w^-1`. The conclusion supplies an actual
smooth datum `rho` on the fine subgroup inside `M_J`, together with an actual
equivariant isomorphism between the entire geometric term and normalized
standard induction of `rho` inside `M_J`. Neither datum has a finiteness or
irreducibility condition.

The hypothesis `PointSourceIntersectionIdentities` supplies the target Levi,
parabolic and radical equalities through
`pointTargetIntersectionIdentities`, which applies the source identities at the
inverse minimum and inverse lift. The fine-index equality follows from
`leviIndex_intersectionLeviIndex` and
`intersectionSubset_eq_simpleImage_inter`. The datum `rho` is the actual
source Jacquet object, transported by the original inverse-conjugation
functor, then by the identity identification of equal target fine Levis,
then by the canonical equivalence with the subgroup inside `M_J`.

The proof specializes the existing natural isomorphism
`geometricTargetInductionComparisonIso` and takes its component at that
transported source object. This published comparison identifies the
semidirect decompositions and their normalized induction functors using the
three literal subgroup equalities. It needs no preservation of finite length,
short-exactness, compact-limit or endpoint input.

`PointProperTargetGeometricTermExclusion` is a Prop-valued input condition:
whenever the intrinsic target intersection is proper, every irreducible
`IsLeviCuspidal` object on `M_J` is excluded as an actual subquotient of the
geometric term. It quantifies over all original data `sigma` and all supplied
decomposition witnesses.

`pointProperTargetGeometricTermExclusion_of_standardInduction` proves this
condition from a uniform exclusion for actual normalized standard induction
inside every coarse Levi. The additional exclusion hypothesis remains explicit
in its full scope. Properness of the intrinsic target intersection implies
`K != Finset.univ`, since the image of a full subtype index is the coarse
index. An alleged actual subquotient of the geometric term is transported
through the preceding actual isomorphism and contradicts the supplied standard
induction exclusion.

The construction is internal transport of existing actual functors, rather
than an assertion quoted from the literature. Its additional declaration-level
dependencies are `levi_le_of_subset`, `leviIndex_subset`,
`isSemidirectDecomposition_in_levi`, `subgroupOfContinuousEquiv`,
`identityConjugationMembership`, and
`SmoothRep.IsSubquotient.of_iso_right`. The last declaration occurs in
`Classification.SupercuspidalSupport`, but its proof uses an actual
injective/surjective subquotient presentation and composition with an
isomorphism; it invokes no classification theorem. No geometric-filtration
or adjointness theorem is invoked here.

The rational-point group retains its canonical `pointTopology` and the displayed
local compactness, nonarchimedean and closedness assumptions. Universes `u`
and `v` are independent and carriers have universe `max (u + 1) v`. There is
no restriction on characteristic, relative rank or nonemptiness of simple roots.
The structural source identities and proper-standard induction exclusion
remain explicit inputs. The former have a separate root-comparison proof; the
latter, and the actual normalized geometric filtration, are still obligations
of the full extraction task.
