# Abelian structure, coproducts and smallness in a Bernstein block

Author: Worker 85. This is supporting, derived work for Renard VI.10.1–VI.10.2.
The block is exactly the published `BernsteinSaturatedBlock`. No statement
identifying that block with a Jacquet-defined block is used.

The block condition asks that every actual irreducible subquotient satisfy
`IsBernsteinInertialSupport` for its prescribed inertial class. The generic
published Serre-class and finite-product results apply to this predicate and
give the inherited abelian structure. The Lean equality in
`bernsteinSaturatedBlock_abelian` records compatibility with the existing
full-subcategory additive structure.

For a family indexed in `Type (max uF uV)`, every irreducible subquotient
of its actual smooth direct sum occurs in one summand, by the published
`SmoothRep.irreducibleSubquotient_directSum`. Thus the direct sum belongs
to the same block. `bernsteinSaturatedBlockDirectSumCofan` is the actual
smooth direct-sum cofan inside the full block; its colimit proof restricts
the ambient universal property. This supplies coproducts at the block's
Hom universe, with no length, admissibility, support-uniqueness or
Bernstein-decomposition assumption.

Finite generation over `MonoidAlgebra ℂ (rationalPoints G)` implies
preservation of these coproducts by the integer-module Hom functor:
the published `SmoothRep.hom_preservesFullSubcategoryCoproducts` applies,
because the actual direct sums have just been proved to lie in the block.
The reason is that a morphism out of a finitely generated group-algebra
module has only finitely many nonzero coordinate maps.

The final theorem takes, explicitly, a block object `P`, lifting along
all epimorphisms, finite group-algebra generation and separation of
morphisms. Lifting gives Mathlib projectivity; separation gives
`IsSeparator P`. Together with the smallness just proved, the published
`Langlands.Renard.preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator`
gives an equivalence to unital modules over `(End P)ᵐᵒᵖ`.

The setting retains arbitrary field and carrier universes, the nonarchimedean
local field, actual group scheme, standard family and inertial class of the
published block. These structural constructions do not prove that the
specific induced representation of VI.10.1 is a finitely generated
progenerator. That representation-theoretic assertion remains an input
when applying the final theorem.

Provenance: derived from the published generic constituent, smooth direct-sum,
finite-generation and small-progenerator results cited by Lean name above.
The application is motivated by David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, VI.10.1–VI.10.2,
printed p.208 / PDF p.214, registered source
`renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof uses the Library's generic categorical theorem rather than
constructing the tensor quasi-inverse in the source.
