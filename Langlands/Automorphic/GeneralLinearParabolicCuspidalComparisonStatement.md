# All-proper and standard maximal-block GL cuspidality

`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearParabolicCuspidalComparisonStatement`
is a proposition target for equality of two existing subrepresentations of the
same `continuousRightAction`. Fix any number field `F` in an arbitrary
universe and any natural rank `n`. The group is the actual general-linear
group scheme `GL_n` over `Spec F`, and the ambient carrier on both sides is
the original `ContinuousRationalFunctions F GL_n`.

The left side is `normalizedParabolicCuspidalSubrepresentation`: constant
terms vanish for every actual proper rational parabolic of this group.
Each period is over the actual rational quotient of the canonical ambient
unipotent-radical image and uses exactly `properParabolicQuotientMeasure`,
the intrinsic mass-one quotient Haar measure. Membership includes absolute
convergence for every adelic argument; the existing compact-radical-quotient
theorem proves that convergence separately for continuous functions.

The right side is `generalLinearStandardBlockVanishingSubrepresentation`.
It uses precisely all splits `a + b = n` with both `a` and `b` positive,
the existing upper two-block unipotent subgroup functors, and their original
`rationalQuotientMeasure`. The existing membership theorem identifies this
condition with `Langlands.Automorphic.IsCuspidal` after the unchanged
`continuousGeneralLinearEquiv`. Thus the target compares all proper rational
parabolics, including nonstandard ones, with the original maximal-block
definition. It asserts equality as subrepresentations, not an abstract
isomorphism of unrelated carriers.

## Explicit hypotheses

The exact universal `ParabolicDynamicStatement` premise `hPD` remains.
Connected reductivity of this actual `GL_n` is an explicit proof parameter
`hG`; the existing `isConnectedReductive_generalLinear` supplies it.
Affineness and smoothness are installed by the proved general-linear
instances. The statement also retains the original
`CompactSpace (AdeleQuotient F)` premise.

No positivity hypothesis on `n` is imposed. The positive-split condition on
the right is empty in ranks zero and one, so the proposed equality includes
the assertion that all-proper vanishing is vacuous in those ranks. No
smoothness, growth, finite-level, compact-finiteness, split-centre invariance
or square-integrability condition is imposed on the functions.

The two subrepresentations restrict the same positive right action
`R(g)f(x) = f(x * g)` of the full actual adelic point group. Their equality
would preserve the original function, every complex value and this action.
It would let the existing standard-block linear equivalence restrict to an
equivalence from the intrinsic all-proper space. This file constructs no
such equivalence and assumes no proof of the equality.

## Source and derived scope

Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
section 1.9, printed pp.34–36 (PDF pp.51–53), describes rational conjugation
to standard parabolics, the subset indexing of standard parabolics, and
the standard block subgroups of `GL_n`. Definition 6.5.1 and (6.18),
printed p.167 (PDF p.181), define cuspidality by every proper parabolic.
Exercise 6.8, printed p.181 (PDF p.195), asks for its reduction to standard
maximal parabolics for automorphic forms or `L2([G])`, with almost-everywhere
vanishing. Section 9.2, (9.7), printed pp.242–243 (PDF pp.254–255), records
absolute convergence of continuous compact-quotient periods. The complete
retained author errata has no correction to section 1.9, Definition 6.5.1
or Exercise 6.8. Its section 9.2 corrections repair later quotient notation
and a character factor; they do not change this compact-period convergence
observation.

The present equality is a derived target on arbitrary continuous
rational-invariant functions, with pointwise vanishing and the exact
Library probability measures. It is not a literal transcription of
Exercise 6.8, an identification with the source's automorphic-form carrier,
or an almost-everywhere `L2` assertion. Rational invariance, continuity and
compact unipotent rational quotients support the same reduction argument
without a growth or differential hypothesis.

The existing `normalizedGeneralLinearParabolicCuspidal_le_standardBlock`
proves the forward containment by selecting each actual positive two-block
proper parabolic, identifying its canonical radical on every test scheme,
and transporting the exact intrinsic block measure comparison.
The reverse direction remains to be proved. One possible route rationally
conjugates any proper `GL_n` parabolic to a standard flag parabolic and
places that standard parabolic inside a standard maximal two-block one.
Its radical contains the latter's radical as a normal subgroup. An
iterated-integral formula for the compact rational quotients then expresses
the smaller parabolic's constant term as a further period of that maximal
constant term. Rational conjugation must transport the actual quotient
and its normalized measure and retain the original function's rational
left invariance.

The fixed diagonal-torus standard-parabolic comparison alone does not
classify every rational parabolic. The rational-conjugation, radical,
quotient-map and iterated-integral identifications in this route remain
proof obligations. The public `GroupSchemeParabolicWeilMeasure` already
derives radical Haar right invariance and counting-measure Weil
compatibility for the unchanged probability family from compactness.
Those results alone supply neither the conjugation nor the iterated-period
identities. None of these identities is supplied as a hypothesis here.

## Boundary

This file defines only the proposition. It proves no reverse containment,
surjectivity or new equivalence. The equality concerns actual continuous
functions before quotienting by the split centre. It asserts no finite
volume, reduction theorem, automatic growth or regularity, cuspidal decay,
Hilbert-space identification or spectral decomposition. A proof must be
published separately before the equality can be used.
