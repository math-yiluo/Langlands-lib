# Closure of actual prime-power torsion

This module defines `PrimePowerTorsion.locus A p` as the underlying points of
actual sections of `A` over the identity test object `Spec K` killed by some
`p ^ n`. The definition works over any field and for any natural number `p`.
The group law, identity, inversion and powers are those of the existing
abelian scheme. No abstract replacement for its torsion points is introduced.
The universe `u` is arbitrary throughout.

The multiplication lemmas identify powers of a section with the actual
multiplication morphism. Over an algebraically closed field, a closed point
of a fibre has a field-valued section. The closed points in that fibre are
dense, so the inverse image of the torsion locus lies in its closure. For
characteristic zero and a prime `p`, geometric point divisibility shows that
multiplication by `p` maps the torsion locus onto itself. Multiplication is
étale and finite, respectively open and closed on the underlying spaces.
These facts give equality of the inverse image and image of the closure
with the closure.

The connectedness argument is an internal topological refinement of the
usual closed subgroup proof. The closure is noetherian and has finitely
many connected components. Its surjective multiplication map induces a
permutation of those components and fixes the identity component. Every
torsion point reaches the identity under some iterate, so injectivity on
components puts all torsion points in the identity component. Their density
in the closure then proves `isConnected_closure_locus`.

The final section proves that sections landing in the closure form
`closureSectionSubgroup A p`, and that translation by any such section
preserves the entire closure. Products and inverses preserve the torsion
locus. Continuity first extends translation stability from torsion sections
to the closure in one variable, then to the other variable; inverse
translation gives equality of images. These subgroup and translation results
hold over every field for every natural number `p`.

This is a derived internal generalization of the published modules
`TwoPowerTorsionClosure`, `TwoPowerTorsionClosureConnected`, and
`TwoPowerTorsionClosureSubgroupProof`. It reuses the generic closed-point
lemma from the first, and imports the noetherian connected-component theorem.
The geometric aim is the prime-to-characteristic torsion-density assertion
in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
version, Chapter V, §3, Theorem (5.30), printed p.84 / PDF p.88, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. The Lean density
application specializes to algebraically closed characteristic-zero fields.
The finite connected-component argument is the implemented route, rather
than a claim to reproduce the literature proof verbatim.
