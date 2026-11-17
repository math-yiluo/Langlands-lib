# Original actual standard integrals under rational conjugation

This internal prerequisite for Waldspurger (2003), V.3 formula (1),
printed p.295 / PDF p.61, registered as `waldspurger-2003-plancherel`,
isolates the exact original-integral conjugation square needed before
continuation and Weyl comparison. It is a target for the actual original
common-Levi standard integrals, not an assumed naturality law for free
operator families. The target remains unproved.

The setting is an arbitrary nonarchimedean local field, an affine locally
finite type connected reductive group scheme, a base cocharacter `χ`, and
two cocharacters `ψ, ψ'` with the same centralizer subgroup functor as `χ`.
The representation carrier universe is independent of the field universe.
The inducing object is any actual smooth representation of the literal
Levi `levi χ`; no induced irreducibility, admissibility, characteristic-zero,
splitness, quasi-splitness or positive-rank hypothesis is imposed. The
source squared-modulus compatibility is the exact existing proposition
needed to define the original actual pairFamily. Source compactness data
consist of the displayed compact open `K` and its compactness proof;
no Iwasawa decomposition is needed for this original-integral target.

The elementary helper `conjugateCentralizer` is proved. It transports the
literal common-centralizer equality through the inverse of the actual
inner scheme isomorphism, using `Dynamic.centralizer_eq_comap_of_iso` and
the category isomorphism identities. Its proof needs no reductivity or
local-field topological assertion.

`commonLeftTranslation` is constructed for each of these parabolics. It
specializes the published actual vector translation to the common
semidirect decompositions, using the actual parabolic, Levi and radical
conjugation comparisons. Radical unimodularity follows from the displayed
connected reductivity via the published theorem. It then lifts the
canonical full-parameter `conjugateTwistEquiv`. Its source is the actual
normalized induction of `A_z` at `ψ`, and its target is the actual normalized
induction of `(gA)_(g z)` at the conjugate cocharacter `ψ ≫ Int(g)`. The
translation component is `f(x) ↦ f(g⁻¹*x)`, with no new scalar or measure.

`ConjugateModulus` is exactly the squared-modulus compatibility proposition
for the two conjugate common-Levi decompositions. `conjugateFullDomainRegion`
is the inverse image under `conjugateParameter χ g` of the actual full
original integral domain for those conjugate parabolics, the canonical
conjugate inducing object and the actual conjugate compact open
`RationalDynamicSource.conjugateCompact g K`. Its measure is the existing
`pairQuotientMeasure` for that compact open and its proved compactness.
This is the full original scalar-integral and carrier-representability
domain, not a denominator-defined continuation region.

`conjugatePairFamily` is precisely the published actual `pairFamily` for
those conjugate data, reparametrized on the above inverse-image domain by
`Set.restrictPreimage`. It introduces no alternative operator or analytic
input. Naming the actual pullback domain and this family makes the target
keep both genuine original families explicit without repeatedly unfolding
their dependent domains.

`OriginalConjugationStatement` is a closed Prop-valued target. For every
set of the above actual data and source squared-modulus proof, it concludes
existence of one conjugate squared-modulus proof, equality of the entire
source full domain with `conjugateFullDomainRegion`, and the original
operator square for every parameter and every original source vector.
The square says that conjugate original standard integration after
`commonLeftTranslation` equals `commonLeftTranslation` after source
original standard integration. Both full-domain proofs are quantified in
the square; the preceding equality guarantees that either one supplies
the other. Thus the statement does not restrict the conclusion to an
arbitrarily assumed overlap.

The character map retains the full rational-character norm algebra and
the conjugate object is the published canonical smooth pullback on the
original carrier. The compact open and all radical, intersection and
quotient Haar data are the source-normalized actual data for `K` and its
canonical conjugate, so the target permits no freely chosen quotient
measure or compatibility map. The same closed target applies to the dual
inducing object; the already published same-functional conjugate-dual
comparison supplies its canonical identification where needed.

Only `conjugateCentralizer` and the displayed translation/parameter
constructions are proved here. The existence of conjugate modulus
compatibility, full-domain conjugation and the actual original integral
square are conclusions of the unproved target. This unit proves no scalar
conjugation theorem, continuation existence, unitary extension, integrated
coefficient identity, V.3 cocycle or Weyl descent law, and does not reassign
the existing owners of those substantive proofs. Same-parameter inducing
representative naturality is already proved as
`DynamicCommonLeviCompact.pairFamily_natural`; the original translated
orbit-base square is proved separately in `ActualCommonLeviBaseChange`.
