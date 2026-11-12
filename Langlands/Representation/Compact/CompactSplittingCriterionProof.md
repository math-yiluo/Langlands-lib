# The compact part splits exactly under (KF)

Author: Worker 88. `compactSplittingCriterion` proves the exact Library
proposition `Langlands.Renard.CompactRepresentation.CompactSplittingCriterionStatement`.
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.7 Proposition and proof, printed
pp.95–96 / PDF pp.101–102, with IV.1.6 and Appendix A.IX, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The exact target quantifies over a Hausdorff locally compact totally
disconnected sigma-compact group with its Borel structure and a supplied
regular two-sided Haar measure. All these hypotheses and the independent
group and representation-carrier universes are retained. The category
factors test actual irreducible subquotients of arbitrary smooth objects;
no finite-length or admissibility restriction is added. The factor indexed
by `true` has all such constituents compact, and that indexed by `false`
has none compact. The finite-level condition is exactly the finiteness of
the published compact-coefficient class stratum with nonzero `K`-fixed vectors.

The entry theorem identifies these factor definitions with the published
`SmoothRep.irreducibleSubquotientProperties` and uses the two implications
proved in its companion files. Those files carry the mathematical proof;
the entry adds no conditional premise or replacement definition.

`CompactSplittingForward` constructs the source's pointwise finite sum of
compact-isotypic projectors. Published unconditional complementarity supplies
each individual projector. A smooth vector is fixed by some compact open
subgroup; (KF) makes all but finitely many component projectors vanish on it.
The published pointwise-sum algebra gives a natural idempotent and identifies
its range with the total intrinsic compact-isotypic part. It acts as the
identity on exactly the compact irreducibles: exhaustion gives one direction,
and compact ambient coefficients on every vector of the total part give the
other. The published natural-idempotent category construction provides the
actual coproduct cofans and off-diagonal Hom vanishing required by A.IX.
Its paired Markdown gives the precise projector laws and hypotheses.

`CompactPartExhaustion` supplies the converse's preliminary fact that an
object all of whose irreducible subquotients are compact is exhausted by its
total compact-isotypic part. If its quotient by that part were nonzero, it
would have an irreducible subquotient `D`, compact by the constituent condition.
Published projectivity of compact irreducibles embeds `D` in the quotient and
lifts that embedding to the original object. The lift's image lies in the
total compact-isotypic part, making its quotient map zero, a contradiction.
This requires neither (KF) nor a chain condition. Its paired Markdown details
the actual injection, surjection and lifting maps.

`CompactSplittingConverse` first proves that a finite group-algebra module
exhausted by its compact isotypic parts admits nonzero maps to only finitely
many compact irreducible classes. Finite generation makes the top of its
submodule lattice a compact lattice element, so finitely many isotypic parts
already span it. Schur separation places all those parts in the annihilator
of every other class, forcing every outgoing map to that class to vanish.

For an open subgroup `K`, the topological quotient `G/K` is discrete and is
a continuous image of a sigma-compact, hence Lindelof, space. It is countable,
and therefore small in every chosen carrier universe. The published
`Jacquet.smallFixedVectorGenerator` is consequently available in the exact
universe `v`. It is the resized compact permutation representation, cyclic
at the identity-coset vector, with its published Frobenius evaluation law.
Use the assumed category decomposition on this generator. Its compact
component is a quotient, via the actual coproduct projection, so remains
finite over the group algebra. It has isotypic exhaustion by the preceding
helper. Every compact irreducible with a nonzero `K`-fixed vector receives a
nonzero map from the generator by Frobenius evaluation. Off-diagonal Hom
vanishing kills the map from the noncompact component, so its restriction
to the compact component is nonzero. The whole stratum thus lies in that
component's finite set of quotient classes. This proves (KF), even for an
open `K` without using compactness of `K` in this implication.

The converse follows Renard's compact-induction and finite-type argument,
expressing its final finite-length consequence directly by compactness of
the top submodule and a finite isotypic cover. The independent-universe
resizing step is explicit. Each companion proof is derived from published
Library constructions and actual maps; no unproved structural assertion,
new axiom, self-review or additional target hypothesis is used.
