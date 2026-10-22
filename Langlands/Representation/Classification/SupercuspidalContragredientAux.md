# Contragredient transfer and conjugate coinvariants

Author: Worker 115.

This module supplies supporting constructions and proved transfer lemmas for
`Langlands.GeneralLinear.SupercuspidalContragredientStatement`. It does not
prove that complete statement. In particular, smooth separation and bidual
reflexivity are explicit hypotheses of the irreducibility transfer lemmas;
this module neither asserts nor assumes them globally.

## Provenance and scope

These are internal derived results from the imported Library definitions,
compact fixed-vector duality, quotient smoothness, and Mathlib's algebraic
representation and duality APIs. No new literature assertion or representation
predicate is introduced. The definition `Jacquet.coinvariantsConjEquiv` is the
map induced by the existing representation action on the actual coinvariant
quotients. Its correctness lemmas and the other transfer lemmas below provide
the consumer interface. Existing Library Lean/Markdown pairs are unchanged.

## Admissibility reflection

`isAdmissible_of_smoothContragredient` assumes a topological group with a
compact-open subgroup inside every open subgroup, a smooth complex
representation, and admissibility of its smooth contragredient. For a compact
open subgroup, `smoothDualFixedRestriction_bijective` identifies the fixed
smooth functionals with the full algebraic dual of the original fixed vectors.
Finite dimensionality of the former therefore implies finite dimensionality
of the latter by `Module.finite_dual_iff`. The published cofinality lemma
`finite_fixedVectors_of_le` passes to each larger open subgroup.

## Irreducibility transfer

`eq_zero_of_smoothDual_annihilates` unwraps injectivity of canonical smooth
bidual evaluation: a vector annihilated by every smooth functional is zero.

`isIrreducible_of_smoothContragredient` requires smooth separation for every
smooth representation in the carrier universe. The universally quantified
hypothesis is used both for the original representation and for an invariant
quotient. For an invariant subspace W, its annihilator inside the smooth dual
is invariant because the dual action precomposes with the inverse action.
Irreducibility of the smooth dual makes this annihilator either zero or all.
If it is zero, every smooth functional on V/W pulls back to zero, and
separation forces V/W to vanish, so W is all of V. If it is all, separation
on V forces W to vanish. The proof also obtains nontriviality of V from
nontriviality of its irreducible smooth dual.

`isIrreducible_iff_of_equiv` transfers the simple-module condition through the
module equivalence attached to an actual representation equivalence.
`isIrreducible_smoothContragredient_iff_of_bidual` adds bijectivity of the
canonical smooth bidual map. It applies the reflection lemma to the smooth
dual and transfers irreducibility across this bidual equivalence to obtain
the converse. These lemmas work for independent group and carrier universes.

## Conjugate coinvariants

For any commutative coefficient ring, group, representation rho, subgroup N,
and group element g, `Jacquet.coinvariantsConjEquiv` sends the class of v
modulo N to the class of rho(g)v modulo gNg inverse. The inverse map uses
g inverse. Conjugation transports the generating quotient relations, and
the two maps are inverse by the representation identities. This needs
neither topology, smoothness nor admissibility.

`Jacquet.coinvariants_conj_subsingleton_iff` transfers vanishing through this
linear equivalence. Consequently `GeneralLinear.isSupercuspidal_iff_standard`
identifies the existing supercuspidal predicate with admissibility and
vanishing at all proper standard block radicals. The implication to standard
radicals uses the identity conjugation; the reverse implication transports
vanishing to every conjugate. All ranks and block shapes are included.
