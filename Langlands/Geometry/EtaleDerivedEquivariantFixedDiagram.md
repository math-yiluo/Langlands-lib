# Fixed-scheme specialization of actual equivariant derived diagrams

This internal construction combines the published actual derived action
diagrams of `EtaleDerivedEquivariantDiagram` with the fixed-scheme
coefficient construction of `EtaleEquivariantFixedDiagram`. It derives
the comparison from actual derived pullback and its identity law.
It introduces no new claim translated from the original literature.

Let `X : Scheme.{u}`, let `R : Type u` be a commutative ring, let an
abstract group act by `ρ : G →* (Aut X)ᵐᵒᵖ`, and let
`D : J ⥤ EquivariantSheaf R ρ` be a diagram of actual equivariant
small-etale module sheaves. The existing `ofFixed` construction regards
it as compatible coefficients on the constant opposite-scheme diagram.
The fixed-scheme sheaf localization instance supplies the same instance
at every vertex; its universe is independent of the module
derived-category localization universe.

`ofFixed_derivedSections_map` identifies each varying-scheme derived
transition with the original coefficient map under
`pullbackDerivedSectionsFunctor`. Its proof expands the transition as
equivariant derived pullback along the scheme identity followed by the
derived coefficient morphism, splits the latter over composition, and uses
the proved equivariant derived pullback identity with its canonical
restriction comparison.

`ofFixedDerivedSectionsIso` identifies the derived action diagram of
the fixed-scheme coefficients with `D` followed by the equivariant
derived-section functor. Its components are identities; the transition
equation just proved supplies naturality along index arrows.
`ofFixedDerivedSectionsFunctorIso` makes this comparison natural in the
whole equivariant sheaf diagram, using its componentwise coefficient
maps. `ofFixedDerivedSectionsIso_hom_app` records its identity components.

`ofFixed_derivedHomology` states that this comparison commutes with the
canonical recovery of ordinary cohomology and with the published
fixed-scheme ordinary-cohomology comparison.
`ofFixed_derivedZero` states the corresponding square for ordinary
sections. Both are equations of natural transformations of action
diagrams, proved at each vertex using the identity law under the
homology functor and the existing canonical recovery components.
No faithfulness of cohomology is assumed.

The index object and morphism universes and the group universe are
independent. All coefficients are sheaves placed in degree zero, over a
fixed scalar ring, and global sections are ordinary. Coefficient
transitions need not be invertible. These constructions do not supply
compact supports, traces, group topology or smoothness, scalar change,
inverse limits, arithmetic Galois specialization or actual Harris
geometric realization.
