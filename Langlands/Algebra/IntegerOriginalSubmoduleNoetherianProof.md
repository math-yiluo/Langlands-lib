# Noetherian criteria for the original nonunital action

Worker 709 prepared this proof of the published ordered aggregate
`Langlands.Algebra.IntegerOriginalSubmoduleNoetherian.IntegerOriginalSubmoduleNoetherianStatement`.
Worker 1088 rechecked it against the published statement, removed two
redundant local bindings, and submitted it.
The aggregate and its three components are imported unchanged from
`Langlands.Algebra.IntegerOriginalSubmoduleNoetherianStatements`.
This proof file defines the component theorems `accCriterion`,
`maximalCriterion` and `chainCriterion`, then assembles their conjunction
as `integerOriginalSubmoduleNoetherian`.

Each component binds an arbitrary possibly noncommutative `NonUnitalRing A`,
an `AddCommGroup M`, and the original `NonUnitalModule A M`. The ring and
carrier universes are independent, in the order `uA, uM`. The left side uses
exactly the local `CompatibleUnitization.module rho`, where
`rho = NonUnitalModule.toIntLinearEndHom (A := A) (V := M)`.
The right sides use the actual additive subgroups stable under that same
original action. No action is replaced. Zero actions and zero carriers are
included, with no unit law, nondegeneracy, finite generation, field or
Noetherian premise.

`accCriterion` unfolds the closed ACC target by introducing its original
inputs. A local `let` names the same selected
`CompatibleUnitization.module rho`, so instance search finds it when
rewriting; no other module structure is introduced. Mathlib's
`isNoetherian_iff` changes ordinary Noetherianity of the
selected unitized module to well-founded strict reverse order on its
submodule poset. The published
`NonUnitalSubmodule.intUnitizedOrderIso` is an order isomorphism from the
original stable additive subgroups to exactly these unitized submodules,
preserving underlying subsets. The forward implication pulls
well-foundedness back through its dual order embedding; the reverse
implication uses the dual embedding of its inverse.

`maximalCriterion` rewrites by `accCriterion`, unfolds `WellFoundedGT`
to well-foundedness of the reversed strict order, and rewrites by
`WellFounded.wellFounded_iff_has_min`.
Its witness belongs to the specified nonempty subset and has no strictly
larger member there. It need not be the greatest member.
`chainCriterion` rewrites by `accCriterion` and
`wellFoundedGT_iff_monotone_chain_condition`. Its chains are genuine
natural-indexed increasing order homomorphisms, and the conclusion is
eventual equality at every later index.

`integerOriginalSubmoduleNoetherian` assembles those three closed theorems
as ACC, maximal-element criterion, and increasing-sequence criterion,
in that order. The proof defines no global instances, categorical
subobjects or additional lattice structure.

This is internal derived content using the project's original-action
integer-unitization order isomorphism and Mathlib's order-theoretic
Noetherian criteria. Renard does not state this integer-unitization
comparison in this form. The motivating original is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read the conventions at printed pages 5–6 / PDF11–12 and
I.2.1 at printed page 14 / PDF20–21 in the parent audit, and reread and
visually checked A.I.2–A.I.3, printed pages 248–249 / PDF254–255.
Worker 1088 independently reread the same three page ranges, after
verifying the file's SHA256, while preparing the published statement pair.
The source uses complex unitization and categorical subobjects, which
are separate from the concrete integer construction proved here.

The source wording repairs and finite-type boundaries in the published
`Langlands/CategoryTheory/RenardFiniteType.md` are retained.
The consulted `notes/renard/appendix-a-corrections.md` concerns other
Appendix A passages. No dedicated project errata file for the 2026
source was found in the earlier audit. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read only at PDF18–19 in that audit. It concerns an older edition
and supplies no author-issued correction for these internal targets.
Renard's bibliography references [25] and [37] have not been read for
this unit and provide no proof evidence.

No comparison with categorical subobjects, source finite type or the
source's possibly nonunital Noetherian-algebra convention follows here.
Finite-generation adapters, full C.II and whole-book completion remain
parent obligations. This unit supplies the exact aggregate proof without
changing the published statement pair or its imported constructions.
