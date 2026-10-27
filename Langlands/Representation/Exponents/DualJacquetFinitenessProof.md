# Finiteness of full-dual opposite Jacquet exponents

Author: Worker 189.

`Langlands.glDualJacquetFiniteness` proves exactly the published proposition
`Langlands.GLDualJacquetFinitenessStatement.{uF,uV}`. The finite p-adic field
universe `uF` and source carrier universe `uV` remain independent. For each
positive rank, standard block shape and irreducible admissible source, the
theorem proves that the actual smooth full-dual opposite Jacquet exponents
form a finite set, every occurring character has a finite least uniform
nilpotence index on its whole generalized component, and the supremum of
these actual generalized components is the full algebraic dual.

The closing declaration explicitly binds its universe parameters as
`.{uField, uCarrier}`, matching the field-then-carrier order of `.{uF, uV}`
in the published target.

The proof uses finiteness of the space of action operators. It imposes no
finite dimensionality on the Jacquet module, its dual or a generalized
component, and adds no hypotheses to the published statement.

## Transposition of the actual action

For a commutative ring, a commutative acting group and a module in independent
universes, `commutativeTranspose_actionSpan_finite` sends the actual action
operator span through the linear map `Module.Dual.transpose`. Its image is
exactly the span of the full transpose action. A linear image of a finite
module is finite. This requires no finite dimensionality of the original
module or its algebraic dual.

`commutativeTranspose_action_isLocallyConstant` postcomposes the locally
constant operator map with the same transposition function. Local constancy
is preserved by postcomposition with any function, so this step requires no
topology on the carrier or its endomorphisms. The existing transpose evaluation
identity identifies that composition with the actual action on the entire
algebraic dual.

These arguments use the existing commutative transpose convention: the dual
action evaluates a functional on the original action, without inversion of
the group element or complex conjugation.

## The split-center operator hypotheses

`splitCentreDualJacquet_actionFinite` establishes finite operator span and
local constancy for the full-dual split-center action, assuming admissibility
of the source and finite generation of its actual opposite Jacquet module
over the Levi group algebra.

It lifts block scalars to the center of the product Levi. Continuity of this
homomorphism follows coordinate by coordinate from the continuous scalar
matrix homomorphisms. The existing theorem
`Langlands.Parabolic.isAdmissible_standardOppositeJacquet` gives admissibility
of the actual opposite Jacquet module. The published
`Langlands.centralActionSpan_finite` and
`Langlands.centralAction_isLocallyConstant` then give the two operator
hypotheses on its split-center restriction. The transpose lemmas transport
both conclusions to its full algebraic dual.

`splitCentreDualJacquet_actionFinite_of_irreducible` discharges that
finite-generation premise. Irreducibility makes the ambient group-algebra
module simple, hence Noetherian and finitely generated. Admissibility
includes smoothness, so the published
`Langlands.Parabolic.oppositeJacquetFiniteGeneration` applies to the actual
opposite quotient with its normalized action. The preceding adapter now
establishes the two operator hypotheses from just the original irreducibility
and admissibility assumptions. The adapters work in all ranks.

## Closing the published target

The final theorem introduces exactly the parameters and hypotheses of
`GLDualJacquetFinitenessStatement` and applies
`Langlands.finiteActionCommutativeSpectrum` to
`(T.splitCentreDualJacquet B A).ρ`, using the preceding adapter.

The three generic conclusions are definitionally the required conclusions.
`T.IsDualJacquetExponent B A χ` means that `χ` has open kernel and its actual
ordinary exponent-one space is nonzero. The generic occurrence predicate is
precisely this predicate, with no change of character. The definition
`T.dualJacquetExponentNilpotenceIndex B A χ` is the same generic
`commutativeCharacterNilpotenceIndex` of this action. Its finite value bounds
the entire generalized component uniformly in both the functional and the
acting element; it is not a vectorwise order, dimension or composition
multiplicity. The supremum in the generic theorem uses exactly these
occurring characters and the same actual generalized submodules, so it spans
all algebraic dual functionals.

## Provenance and dependencies

This is a derived internal proof of the existing statement, using the
published generic algebraic spectrum theorem and the published representation
theoretic finite-generation and admissibility results. The implementation
follows the finite operator algebra route rather than assuming finite
dimensionality of the carrier or a supplied spectral decomposition. Worker 23
proved the imported generic spectrum and opposite finite-generation theorems;
their implementations are reused by import, without copying their code.

No coefficient realization, scalar quotient extraction, analytic temperedness,
weakly critical support or downstream classification theorem is used. The
target statement pair and all its imported pairs are unchanged.
