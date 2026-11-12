# Homogeneous sections and Renard's literal induction map

This pair constructs the homogeneous base, point restriction, and the maps
from sections to the published induction models in Renard 2026, III.3.2,
printed pp.84–85 / PDF pp.90–91. It constructs the displayed map `α` and its
intrinsic covariance, support, equivariance and naturality laws. Its
bijectivity, the construction of the inverse `β`, and the sheaf induction
functor and categorical equivalence remain separate work.

All names below have prefix
`Langlands.Sheaf.Renard.HomogeneousSections`.

`homogeneousAction H` uses the published
`Langlands.Geometric.leftQuotientAction H ⊤` and Mathlib's
`Subgroup.topEquiv` to obtain the full group action on the existing
`Langlands.Induction.LeftQuotient H`. Its formula is precisely

`g • quotientMap H k = quotientMap H (k * g⁻¹)`.

The action definition is instance-reducible and is installed locally in
this module; consumers should install the same definition when using its
functors. `origin H` is the identity coset, and `subgroup_fixes_origin`
proves that the original subgroup fixes it. `homogeneousContinuousSMul`
derives joint continuity from the published top-subgroup action by
continuous pullback. `quotient_isLocallyProfinite` retains Hausdorffness
and the compact-open neighborhood basis when `G` has these properties and
`H` is closed: use the published Hausdorff quotient result, refine a
preimage neighborhood in `G` to a compact open, and take its image under
the original open continuous quotient map.

`stalkRepresentation H F` is the original fixed-stalk representation at
`origin H`, obtained by the published `SectionActions.fixedStalkFunctor`.
It is not a supplied coefficient representation or a substitute fibre.
`pointRestriction` uses the source's locally profinite group and closed
subgroup hypotheses to lift this original-stalk functor into smooth
representations, through `SmoothStalkRestriction` and the preceding
quotient compact-open basis construction.

`alphaFunction H F s g` is literally the original global germ at the origin
of `globalRepresentation F g s`. Its covariance is

`alphaFunction H F s (h * g) = stalkRepresentation H F h (alphaFunction H F s g)`.

`alphaFunction_covariant` is the published original germ/stalk transport
law applied to the global section arrow with inverse label. The identity
and product conventions are exactly those used in the already published
fixed-stalk and global representations. `alphaEquivariant` bundles this
formula as a complex-linear map into Mathlib's actual covariant-function
module, reused as `Langlands.Induction.EquivariantFunctions`.
`alphaGlobal` is the corresponding intertwiner into the existing
right-translation action `equivariantAction`.

`alphaSmoothGlobal` applies the published `Langlands.smoothMap` to restrict
both actions to their actual smooth vectors. Its target is the published
`Langlands.Induction.smoothInduced H (stalkRepresentation H F)`. This map
needs no prior smoothness assertion on all global sections.

`alphaCompactEquivariant` restricts `alphaGlobal` along the original
compact-section inclusion. For an object of Renard's smooth-action
category, `alphaCompactToSmooth` uses its whole-compact-section smoothness
and the published `Langlands.smoothLift` to put every such image in
`smoothInduced`. No smoothness conclusion is assumed for an arbitrary
function or replaced by pointwise local constancy.

The nonvanishing law `alphaFunction_ne_zero_iff` identifies a nonzero
value at `g` with a nonzero original germ of `s` at `quotientMap H g`.
It follows in both directions from the published `germ_action_zero`
using the two inverse group operators. Consequently,
`quotientSupport_alphaFunction` identifies the actual projected nonzero
support of the induced function with the original section's germ support.
This exact equality supplies compactness for `alphaCompact`, whose target
is the published `Langlands.Induction.compactInduced`. This definition
retains the original compact-section source and the existing covariant
functions with a uniform open right stabilizer and compact support modulo
`H`; there is no parallel induction model.

The two `_apply` formulas expose the literal source formula after the
smooth and compact restrictions. `alphaFunction_naturality` uses the
original stalk map of an actual equivariant sheaf morphism. The two
naturality equations commute with the published `compactInducedMap` and
`smoothInducedMap`, respectively, and with the original compact-section
map and smooth part of the original global-section map. Their proofs use
ordinary stalk-map naturality and the original global equivariance square.

The base-action construction and its topology laws permit an arbitrary
group universe. The section and induction maps use a group in `Type`, as
required for the actual complex coefficient field and the published
compact-section interface on the quotient base. No section-space topology,
finite-dimensionality, second countability or open-subgroup hypothesis is
introduced. The map constructions themselves work for every subgroup;
`pointRestriction` explicitly retains a locally profinite group and closed
subgroup. This module starts with the concrete quotient `H \ G`. It does
not assert that an arbitrary transitive action is isomorphic to that
quotient. That separate source assertion must retain Renard's
countability-at-infinity hypothesis and remains an obligation.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.3.2, printed p.84 / PDF p.90
(inverse right quotient action and point restriction), printed p.85 /
PDF p.91 (literal `α`, compact and smooth-global induction and naturality),
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
