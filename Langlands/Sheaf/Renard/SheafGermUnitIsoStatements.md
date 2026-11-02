# Renard II.2.1: canonical germ-unit invertibility on sheaves

Worker 1227 states the proposition family. Worker 6 contributed the original-source
audit, focused specification and universe design. These are `Prop`-valued
definitions, with no proofs of the stated assertions.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, the first remark on printed
p.37 / PDF p.43. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.41–43 were read directly, and pp.42–43 were also checked visually.
The remark says that if the original presheaf is a sheaf, its natural
identification with the sheaf of sections of its germ space is the canonical
map itself. The preceding construction on printed p.36 / PDF p.42 sends an
original section to its family of original germs, then constructs descent by
gluing the images of local original representatives in a target sheaf.
Specializing that descent to the identity gives the inverse specified here.

The module imports the published `GermDescent` interface, which also imports
the actual canonical units, universe lifts, germ-section sheaf and corrected
target-sheaf separation construction. The
[source-error audit](../../../notes/renard/basis-sheafification-source.md)
explains the false arbitrary-presheaf separation inference in (II.2.1.3).
The published descent instead compares image sections on every smaller basis
open in an overlap and uses separation in the target sheaf. The present
statement uses that actual descent and an actual input sheaf.

All declaration names below have prefix `Langlands.Sheaf.Renard`. The space
is any `X : Type u` with its supplied topology and any chosen
`B : OpenBasis X`. The original section universe `v` is independent of `u`.
The published `GermSections` are locally represented families of the
original stalks and have carrier universe `max u v`.

| Proposition definition | Exact assertion |
| --- | --- |
| `SheafSectionGermsBijectiveStatement G` | For every `U : BasisOpen B`, `Function.Bijective (sectionGerms G.obj.obj U)`. The map goes directly from original sections in universe `v` to their locally represented germ families in `max u v`. |
| `SheafGermLiftUnitIsIsoStatement G` | `IsIso ((germSheafLiftUnit.{u,v} B).app G.obj)`, a statement about the actual component in the normalized presheaf category, with source the actual `presheafLiftJoint` of `G.obj`. |
| `SheafGermLiftUnitNatIsoStatement B` | Existence of a natural isomorphism from `sheafLiftJoint.{u,v} B` to `sheafForget.{u,v} B ⋙ germSheafFunctor.{u,v} B`, whose forward component, after `sheafForget.{u,max u v} B`, is exactly `germSheafLiftUnit.app G.obj` and whose inverse component is exactly `liftedGermDesc.{u,v} (𝟙 G.obj)`. |
| `SheafGermUnitIsIsoStatement G` | For a sheaf with original value universe `max u v`, `IsIso ((germSheafUnit.{u,v} B).app G.obj)`, using the actual direct canonical unit. |
| `SheafGermUnitNatIsoStatement B` | At original value universe `max u v`, existence of a natural isomorphism from the identity on `BasisSheaf.{u,max u v} B` to `sheafForget.{u,max u v} B ⋙ germSheafFunctor.{u,max u v} B`, with underlying forward component exactly `germSheafUnit.app G.obj` and inverse component exactly `germDesc.{u,v} (𝟙 G.obj)`. |

Each natural isomorphism is existentially quantified in the conclusion.
Its type includes naturality and both inverse laws. The equations are
required for every input sheaf and fix both maps to the published
constructions.

`RenardSheafGermUnitIsoStatement.{u,v}` is the closed aggregate: it
quantifies over `X : Type u`, every supplied topology and every chosen basis,
then conjoins all five assertions for every sheaf of the indicated value
universe. The bijectivity assertion and the direct unit and natural-isomorphism
assertions express the source remark. The lifted assertions expose the
internal universe packaging needed to express the same canonical
identification for an arbitrary original value universe `v`.
The lift is the published actual `ULift` functor; no universe comparison or
functor lowering arbitrary larger-valued objects is assumed.

No intersection closure, Hausdorffness, local compactness, countability or
nonemptiness assumption is imposed. Empty spaces and all basis opens,
including empty basis opens when present, remain quantified. The propositions
assume no adjunction or replacement isomorphism. Proofs of this family,
universal Hom correspondences and adjunctions, the following paragraph's
basis/all-open equivalence, compact sections and scalar-module constructions
remain separate obligations.
