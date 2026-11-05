# Conditional category decomposition by compact restriction

Worker 491 defines the all/no arbitrary-subquotient factors for the actual
subgroup-restriction compact-coefficient property and assembles their conditional
category decomposition. This is an internal consequence of the imported
normal-subgroup projector splitting, coefficient permanence, complementary
coproduct construction and nonzero-image Hom argument.

For a subgroup `N` of a group `G` with any topology,
`SmoothRep.compactRestrictionSubquotientProperties N` is the existing
`SmoothRep.subquotientProperties` construction applied to
`SmoothRep.compactRestrictionProperty N`. At `true`, every actual smooth
subquotient has compact smooth-dual coefficients after restriction to `N`.
At `false`, every nontrivial actual smooth subquotient fails that property.
The quantifiers range over arbitrary actual subquotients, with no irreducibility,
finite-length, admissibility or dimension restriction. The group and
representation-carrier universes are independent.

The off-diagonal Hom theorem is the existing nonzero-image argument applied to
this property. The actual image of a nonzero morphism is a nontrivial subquotient
of both objects, so the all/no requirements contradict each other on that image.
This step uses neither normality nor a compact-open or splitting hypothesis.

For the coproduct construction, assume that `G` is a topological group and `N`
is normal, nonarchimedean and weakly locally compact with its actual subgroup
topology. The first decomposition theorem retains all four analytic inputs of
`decomposition_of_normalSubgroup_compactCoefficients`:

1. Every intrinsic compact-class isotypic subrepresentation and its intrinsic
   annihilator are complementary.
2. The set of compact-coefficient classes with nonzero fixed vectors is finite
   at every compact open level.
3. Every total intrinsic isotypic subrepresentation has compact smooth-dual
   coefficients.
4. Every compact-coefficient object is exhausted by its total intrinsic
   isotypic subrepresentation.

The imported splitting produces actual ambient invariant subspaces `S,Q` with
complementary underlying submodules. The restriction on `S` has compact
coefficients. Compact open subgroups of `N` are cofinal by the published
identity-neighborhood basis theorem. The arbitrary-subquotient permanence
theorem therefore places the actual representation on `S` in the `true` factor.
The splitting's exclusion law says that each compact-restriction subquotient of
the actual representation on `Q` is a subsingleton. It consequently cannot be
nontrivial, which gives the `false` factor.

The complementary-coproduct construction supplies the actual inclusion cofan,
with ambient object as vertex, and its full colimit universal property.
Combining it with the proved off-diagonal Hom law yields exactly the existing
`Renard.IsCategoryDecomposition` predicate. No global coproduct-existence
assumption or carrier resizing is used.

The second theorem removes inputs 3 and 4 using the published
`totalIsotypicSubrepresentation_hasCompactSmoothDualCoefficients` and
`totalIsotypicSubrepresentation_eq_top_of_compactCoefficients`.
It assumes that `N` is Hausdorff, locally compact and totally disconnected,
has a Borel measurable structure, and is supplied with a left Haar measure.
Inputs 1 and 2 remain explicit. It does not require countability or
right-invariance of that measure.

Renard VI.3.5 (French edition dated 9 July 2026, printed pp.146–147 / PDF
pp.152–153) motivates the construction; A.IX (printed p.268 / PDF p.274) fixes
the category-decomposition convention. The implemented proof is the imported
conditional splitting followed by the exact factor-membership and coproduct
arguments above. This intermediate unit does not prove the remaining analytic
inputs for the actual rational norm kernel, identify compact restriction with
proper-standard cuspidality, or prove the unchanged whole-cuspidal target.
None of its additional hypotheses is added to that final target.
