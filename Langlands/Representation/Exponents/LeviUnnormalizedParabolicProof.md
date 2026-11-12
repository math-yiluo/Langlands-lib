# Renard VI.1.1: the unnormalized parabolic functors

Worker 124. Module
`Langlands.Representation.Exponents.LeviUnnormalizedParabolicProof` proves
`Langlands.Aubert.General.RepresentedParabolic.leviUnnormalizedParabolicStatements`
with type exactly the unchanged Library proposition
`Langlands.Aubert.General.RepresentedParabolic.LeviUnnormalizedParabolicStatements`.
The field universe `u` and the two carrier universes `v` and `w` remain
independent. No hypothesis is added.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The target is VI.1.1, printed pp.134–135 (PDF pp.140–141); VI.1.2 gives the
normalization conventions on printed pp.135–136 (PDF pp.141–142). Worker 124
read these three PDF pages. No source-specific errata file was found in the
Library or project `notes/errata` locations.

The theorem applies to every actual rational parabolic in the published
represented-parabolic interface: a connected reductive group over any
nonarchimedean local field, a rational Levi, a matching geometric unipotent
radical and their multiplication isomorphism. It retains the target's
local compactness and nonarchimedean-group assumptions on the ambient point
group. The corresponding properties of the Levi's own point group are
proved by the published transport results. There is no admissibility,
finite length, standardness or root-presentation assumption.

The proof has three named clauses, assembled by conjunction into the entry
theorem. The auxiliary constructions in `UnnormalizedParabolic` are internal
proof devices for the actual subgroup images. They are derived from the
published quotient, induction and twist constructions; they do not replace
any object in the statement.

## Evaluation and the radical quotient

`leviUnnormalizedFrobeniusReciprocity` uses the auxiliary linear equivalence
`UnnormalizedParabolic.equiv`, constructed directly for a semidirect
parabolic decomposition `P = M U`.

For an intertwiner `F : π → Ind_P^G σ`, `evaluation` sends `x` to
`(F x)(1)`. Equivariance of `F` identifies evaluation on `π(g)x` with
`(F x)(g)`. Covariance of induced functions then gives
`evaluation(π(p)x) = σ(proj(p)) evaluation(x)`. The projection kills `U`,
so `Jacquet.Localization.lift` descends this map through precisely the
relation quotient in the target, with trivial character. Its covariance on
`M` proves that the descended map intertwines the unnormalized Levi action.

Conversely, a Levi intertwiner `f : π_U → σ` gives the orbit function
`g ↦ f([π(g)x])`. Every `p` factors as its Levi projection times an element
of `U`; the radical acts trivially on its coinvariants. This proves the
required parabolic covariance. The orbit construction is equivariant, and
`smoothLift` uses smoothness of `π` to give smooth induced vectors. Evaluation
of orbit functions and the identity element prove the two inverse laws;
linearity is checked on quotient classes.

Finally, `intertwiningPullbackEquiv` transports the Levi-image action along
`leviPointsEquiv` to the Levi's own rational points. The resulting equivalence
satisfies the target's literal formula
`e F (Jacquet.Localization.mk π.representation U 1 x) = (F x)(1)` by
reflexivity. As in the target, a separate categorical naturality clause is
not asserted.

## Exactness

`leviUnnormalizedFunctorsExact` proves induction exactness using the published
injectivity, middle-exactness and surjectivity results for the actual smooth
induction postcomposition maps. Pullback to the Levi image and inflation
leave the underlying linear maps unchanged. The published continuous Levi
projection proves smoothness of the inflated representations. Affineness and
smoothness of the connected reductive group give a Hausdorff rational-point
group and cofinal compact open subgroups, supplying the remaining hypotheses
of the induction surjectivity theorem.

For Jacquet restriction the proof applies the Jacquet clause of
`leviParabolicFunctorsExact`. Normalization twists the action on exactly the
same radical quotient and leaves the underlying linear maps unchanged;
therefore its injectivity, surjectivity and range/kernel equality are
definitionally the requested unnormalized properties. That published theorem
proves the compact-subgroup property of the actual unipotent radical and
uses character-localization exactness; no such property is assumed here.

## Limits and colimits

`leviUnnormalizedFunctorsPreserveLimits` handles the stated diagram sizes
`PreservesLimitsOfSize.{v,v}` and `PreservesColimitsOfSize.{v,v}`.

For Jacquet colimits, `UnnormalizedParabolic.jacquet_preservesColimits`
compares the underlying module functor with restriction to `U` followed by
ordinary algebraic coinvariants. The comparison is the published
`Jacquet.Localization.trivialEquiv`, natural on quotient classes. Smooth
inclusion into algebraic representations preserves colimits by its
smooth-part right adjoint. Restriction and algebraic coinvariants preserve
colimits, and the forgetful functor from smooth representations to modules
reflects them. This proves the desired colimit preservation before, and
then after, transport to the actual Levi points.

For induction, `characterTwistEquivalence` constructs the equivalence given
by a smooth scalar character and its reciprocal. `cancelNormalizationIso`
identifies inverse-half twisting followed by normalized induction with the
literal unnormalized induction composite. The radical's unimodularity is
proved by `isUnimodularModulus_pointImage_radical`; the published identity
`closedHalfCharacter_eq_comp_projection` therefore identifies the induction
character with the half character of the Levi projection. The two scalar
factors cancel. The resulting natural isomorphism keeps every value of an
induced function unchanged.

The proof transfers limit preservation from the published normalized
induction theorem through this twist equivalence. For colimits it uses the
published smooth-twist colimit preservation and normalized induction colimit
preservation. The latter's compact quotient hypothesis is supplied by the
unconditional `arbitraryParabolicQuotientCompact`, and its topological
hypotheses by the same actual-point results used for exactness. Finally,
`SmoothRep.pullbackEquivalence` gives preservation under transport from the
Levi's own point group. These operations preserve the original size `v`;
no identification of `u`, `v` or `w` occurs.

The implemented proof differs from Renard's route for the final Remark:
it transfers the already proved normalized preservation properties rather
than constructing the right adjoint described in the source. It proves
exactly the Remark's colimit conclusion requested by the Library statement.
The statement's Lean/Markdown pair and all of its imports are unchanged.
