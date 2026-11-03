# Actual relative-root rank-one factorization

`Langlands.GroupScheme.RootRankOneFactorizationStatement` is an unproved
proposition at arbitrary universe `u`. It concerns a connected reductive
group scheme `G` over any field `k` and an actual maximal split torus
`i : T → G`. It asserts `RelativeRoot.HasRankOneFactorization i`.

For every actual relative root `a ∈ relativeRoots i` and every nonidentity
rational point `u` in the already defined subgroup functor
`RelativeRoot.subgroup i a`, there is a unique ordered pair `(u′, u′′)` of
rational points in `RelativeRoot.subgroup i (-a)` for which
`m = u′ * u * u′′` belongs to `normalizerPoints i`. This is the predicate
`RelativeRoot.IsOppositeFactorPair i a u (u′, u′′)`. Uniqueness ranges over
all pairs satisfying those membership and normalization conditions.

Every such pair has `u′ ≠ 1` and `u′′ ≠ 1`, and the class of `m` in the
existing quotient `relativeWeylGroup i` satisfies `IsRelativeReflection i a`.
The normalizer subtype uses exactly the normalization proof in the pair
predicate. Thus the conclusion refers to the actual rational normalizer
and its actual quotient action on the rational relative-root span.

If `(2 : ℤ) • a` is not a relative root, the statement also requires
`u′ = u′′`, `u′ = m⁻¹ * u * m`, and `m * m ∈ (rationalPoints.map i).range`.
The last subgroup is the image of the actual map `T(k) → G(k)`. Equal
opposite factors are required only under this nonmultipliable-root
condition; the general statement permits different factors.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 2.11.17 and Remark 2.11.18, printed p.136 (PDF p.167; the remark
ends on PDF p.168), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The proposition is stated
for connected quasi-reductive groups over arbitrary fields, so connected
reductivity is a specialization. The authors' *Corrections and additions*
(version of 1 November 2024), registered as `kaletha-prasad-2024-corrections`,
has no change to Proposition 2.11.17 in its Chapter 2 corrections, PDF
pp.24–26. Remark 2.11.18 explicitly warns that the two opposite factors
need not coincide for a multipliable root.

The cited original is Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Proposition C.2.24(i),(iii) and its proof, printed
pp.620–622 (PDF pp.646–648), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. Its hypothesis on weights of
the unipotent radical is automatic for connected reductive groups. Its
reflection acts on the character lattice and hence induces the reflection
required here on the relative-root span. This file states the
connected-reductive specialization of parts (i) and (iii); it does not
state the extension-field centralizer equivariance of part (ii).

The actual character-orbit-extension subgroup functors, rational points,
normalizer quotient and reflection predicate are the existing Library
constructions. There is no chosen model of a root group, generic
cocharacter, or root-system realization in the hypotheses. Splitness is
assumed only for the maximal split torus; there is no splitness assumption
on `G`, perfectness or characteristic restriction on `k`, reducedness
assumption on the roots, or positive-rank assumption.

No factorization or reflection existence is proved here. In particular,
the implication is quantified over nonidentity root points and does not
itself assert that any such point exists. Constructing these points and
proving the full relative Tits-system target remain separate obligations.
