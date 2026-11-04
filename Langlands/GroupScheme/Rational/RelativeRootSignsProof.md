# Actual relative-root signs determine dynamic subgroup functors

Author: Worker 1309.

`Langlands.GroupScheme.relativeRootSignsDetermineDynamic` proves exactly
`Langlands.GroupScheme.RelativeRootSignsDetermineDynamicStatement.{u}` from
[`RelativeRootSignsStatement`](RelativeRootSignsStatement.md). It retains every
universe `u`, field `k : Type u`, connected reductive group scheme over `Spec k`,
maximal split torus inclusion, and pair of cocharacters in that statement.
The antecedent is precisely its three sign equivalences on every actual relative
root. The conclusions identify the Dynamic parabolic, centralizer and
identity-limit subgroup functors on every test scheme.

The proof first compares the actual generated semigroup subgroups.
`RelativeRoot.semigroupSubgroup_eq_of_relativeRoot_iff` says that membership
agreement at zero and at every actual relative root suffices. It applies the
published `rootSupport_imp_iff_actionWeightSupport_imp` in both directions to
extend rootwise implications to the full ambient conjugation-weight support.
The published `semigroupSubgroup_mono_on_weightSupport` then gives both
inclusions of generated subgroup functors.

These imported support lemmas use the intrinsic action on dual-number tangent
points and the published identification of its weight spaces with adjoint
weight spaces. Every nonzero character in that ambient support is an actual
relative root. The generated subgroup is the subgroup closure, on each test
scheme, of all smooth connected closed stable subgroups with support in the
specified semigroup. Restricting semigroup containment to the ambient support
therefore suffices for containment of these actual subgroup functors.

`RelativeRoot.pairingSemigroupSubgroups_eq_of_relativeRootSigns` applies the
first lemma to the nonnegative, zero and strictly positive integer pairing
regions. The three rootwise membership equivalences are exactly the three
clauses of the sign hypothesis. At the zero character, linearity makes both
pairings zero: the nonnegative and zero membership predicates hold for both
cocharacters, and strict positivity fails for both. This argument includes an
empty relative-root set and zero or nongeneric cocharacters.

The final theorem applies the published
`RelativeRoot.dynamicSemigroupComparison`, imported from
[`DynamicSemigroupProof`](DynamicSemigroupProof.md), separately to the two
cocharacters. Connected reductivity supplies smoothness, affineness and
connectedness of the ambient group. The maximal split torus hypothesis supplies
the split torus required by that comparison. For each of the three regions,
the Dynamic-to-semigroup equality for the first cocharacter, the semigroup
equality just proved, and the reversed comparison for the second cocharacter
give the required Dynamic equality. Every equality is an equality of
`SubgroupFunctor` objects.

This is an internal derivation from the published support and comparison
results. Its only assumptions are those in the unchanged target. It imposes
no condition on characteristic or perfection of the field, splitting of the
ambient group, reducedness of the relative roots, or genericity of a
cocharacter. It assumes no additional realization or uniqueness proposition.

The source context is Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), §2.11, Propositions 2.11.1–2.11.3, printed pp.130–131 / PDF pp.161–162,
and Conrad, Gabber and Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition 3.3.6 and its proof, printed pp.109–110 / PDF pp.135–136.
The registered Kaletha–Prasad *Corrections and Additions* (1 November 2024),
PDF p.25, preserves the conclusions used here. The implemented proof identifies
the generated semigroup subgroups directly on ambient support and uses the
published halfspace comparison; it does not separately invoke the general
uniqueness assertion of Proposition 3.3.6.
