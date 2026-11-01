# Actual direct sums of original nonunital modules

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, I.6, first proposition and the direct-sum
construction in its proof, printed p.27 / PDF33. The same construction is used
in I.5.2, printed pp.26–27 / PDF32–33, to form a projective presentation.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The nondegeneracy definition and finite-upper-bound property are I.1.2,
printed p.7 / PDF13. The adjacent 2010 corrections do not change this construction.

This unit implements the actual direct sum and its intrinsic universal property.
It supplies a construction needed by the cited proofs, rather than the whole
I.6 completeness, cocompleteness, AB5, AB6 or filtered-exactness assertion.
The source's construction uses only additive groups and original ring actions,
so it applies to arbitrary nonunital rings, including the complex algebras used
in I.5.2 and I.6. No unit law is added to the actions.

For a family `M : I → Type uM`, `Carrier M` is literally the dependent
finitely supported function type `Π₀ i, M i`. Its abelian group is Mathlib's
ordinary direct-sum group. `action` applies each original action on every
coordinate, using `DFinsupp.mapRange`; the module laws hold coordinatewise.
`smul_apply` and `smul_single` expose the formulas. The ring, index and summand
universes are independent; the resulting carrier lies in `Type (max uI uM)`.

`inclusion M i` is the original singleton additive map, now packaged as an
actual intertwiner. `desc M f` assembles a family of original intertwiners by
Mathlib's finite-support additive sum. Its action law follows by induction on
zero, singleton vectors and addition. `desc_inclusion` is its value on each
summand, and `hom_ext` proves uniqueness for entire original intertwiners.

If the ring is idempotented and every summand is nondegenerate,
`isNondegenerate` proves nondegeneracy of the actual sum. It inducts on the
same finite-support construction: zero is fixed by zero, a singleton is fixed
by an idempotent fixing its only possibly nonzero coordinate, and the sum of
two vectors is fixed by a common upper bound of their fixing idempotents.
The published absorption law transports fixedness to that common bound.
There is no bound on the cardinality of the family or dimension of a summand.

For a family `P : I → NondegenerateModuleCat A`, `object` bundles this same
carrier and action, `cofan` consists of these same singleton inclusions, and
`cofanIsColimit` packages `desc`, its summand equations and uniqueness in
Mathlib's full `IsColimit` interface. The category's carrier universe is
explicitly `max uI uM`; the index universe must fit there for the finite-support
carrier to be an object of that category. The declaration does not assert
coproduct existence for index types larger than the chosen carrier universe.
No global coproduct instance or resizing axiom is introduced.

The final unapplied examples expose the independent action universes and the
full cofan universal property. Projectivity, enough projectives and the later
I.6 axioms remain separate results.
