# Renard III.3.1–III.3.2: actions, distributions and compact sections

This construction implements the action and smoothness definitions of David
Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, III.3.1, printed p.83 / PDF p.89, and the category and `Γ_c` of
III.3.2, printed p.84 / PDF p.90. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The three source pages of III.3 were read directly; the induction formulas on
PDF p.91 were also checked visually.

All names in this pair lie in `Langlands.Sheaf.Renard.SectionActions`.

`ActionSheaf G X` is an abbreviation for the published
`Langlands.Sheaf.Equivariant.TopologicalSheaf G X (ModuleCat ℂ)`.
It introduces no replacement sheaf object. Its transport-category
presheaf assigns complex vector spaces to opens and linear maps to
group-labelled arrows; its restriction to label-one inclusions is an
ordinary sheaf. Its morphisms are exactly the published natural
transformations, commuting with restrictions and group transport.
`underlying` is the published forgetful functor evaluated on an object.

For a fixed left action of `G` on `X`, a transport arrow `U → V` labelled `g`
means `g • U ⊆ V`. Contravariance sends this arrow to sections on `U`.
The published `translationIso` is invertible, and `gamma` abbreviates
`translateSections`, its induced isomorphism from sections on `U` to
sections on `g • U`. On the whole space the published `sectionArrow g`
has label `g⁻¹`; this gives Renard's left representation convention.
The transport functor's identity and composition laws encode the identity
and product laws of the sheaf action. `global_one` and `global_mul`
expose these laws on global sections. `gamma` is the entire moving-open
isomorphism, rather than just its whole-space component.

The fixed underlying action in the continuous-action section has the
typeclass hypothesis `ContinuousSMul G X`, expressing joint continuity
of `G × X → X`. Renard's ambient spaces are locally compact Hausdorff
totally disconnected spaces, and his group is a topological group with
those properties. The definitions here also make sense on more general
spaces; no theorem extending any of his assertions beyond those
hypotheses is claimed. The action-sheaf abbreviation and its ordinary
global representation themselves need only the topological space and
algebraic action; the later constructions explicitly assume joint
continuity. No topology is imposed on section spaces.

`compactRepresentation` is exactly the published
`CompactSections.representation F.obj`. Its carrier is the existing
`Langlands.Sheaf.CompactSupport.submodule`, using the set of points
where the germ of a global section is nonzero. The published support
transport and compact-support preservation results supply this
representation; compact sections are not reconstructed.

`IsSmoothAction F` is the published representation predicate
`Langlands.IsSmooth` on this *whole* compact-section representation:
each compact section has an open fixing subgroup. This is Renard's
literal definition. The already published `IsSmoothSheaf` instead uses
local fixed sections on invariant neighborhoods, and the already
published `SmoothCompactSections` takes the smooth part of a compact
representation. Neither is substituted for Renard's condition, and
no equivalence with the local predicate is asserted by this pair.
The new predicate selects a full subcategory of the same published
equivariant sheaf category.

`Distribution F` is the algebraic complex-linear dual of those compact
sections. `IsInvariantDistribution F T` says
`T (γ_g s) = T s` for every `g` and `s`. This is equivalent to
fixedness under the contragredient convention
`(g · T)(s) = T (γ_{g⁻¹} s)`, by replacing `g` with `g⁻¹`.
It does not require a topology or continuity of `T`.
`invariantDistributions` is the actual linear subspace defined by
this equation; its zero, addition and scalar laws are proved directly
by evaluating linear functionals.

`SmoothActionSheaf` is Renard's category for this fixed action, with
the existing equivariant sheaf morphisms. `gammaC` lifts the published
`CompactSections.functor` through the published category `SmoothRep`
using the object's *given* `IsSmoothAction` proof. Thus its carrier
contains every compact section. `gammaCToRepIso` is the standard
full-subcategory lift comparison; `gammaC_representation` and
`gammaC_map` record the unchanged representation and intertwiner.
These are construction laws, not proofs of the III.3 propositions.

The space and section carriers are in `Type` (universe zero), while the
group universe `uG` is independent. This is the size specialization
required by the existing compact-section infrastructure when its
coefficient ring is the actual `ℂ`; no universe resizing is claimed.
No finite-dimensionality,
admissibility, countability, or nonempty-space condition is added.
The restriction and homogeneous-induction functors, the sheaf/module
comparison, the coinvariant sheaf, and the III.3.1–III.3.2 statements
remain separate units of this task.
