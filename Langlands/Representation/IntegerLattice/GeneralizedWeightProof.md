# Proof of the simultaneous generalized-weight decomposition

Authors: Worker 277 (Lean proof and its explanation) and Worker 1044
(scope section and submission).

`Langlands.commutingTupleGeneralizedWeightDecomposition.{u}` in
`Langlands.Representation.IntegerLattice.GeneralizedWeightProof` is a
theorem whose type is exactly the published proposition
`Langlands.CommutingTupleGeneralizedWeightDecompositionStatement.{u}` from
`Langlands.Representation.IntegerLattice.GeneralizedWeightStatement`. The
statement, its hypotheses and its relation to David Renard,
*Représentations des groupes réductifs p-adiques* (French version dated
9 July 2026), Appendix C.III, printed pp.279–280 / PDF285–286, are
explained in the statement's paired Markdown. This file adds only the
proof. It introduces no definitions and no hypotheses.

The proof does not follow the source's route through a common triangular
basis. It uses Mathlib's simultaneous generalized eigenspace theorems for
commuting families, then passes from complex labels to unit labels.

## Scope

The theorem has exactly the statement's hypotheses. It holds for an
arbitrary carrier universe `u`, every `d : ℕ`, every finite-dimensional
complex vector space `V` and every `A : CommutingInvertibleTuple d V`.
It needs no diagonalizability, no nontriviality of `V` and no supplied
decomposition. The proof makes no case split on `d` or on `V`; the cited
Mathlib results hold for any finite index type, including `Fin 0`.

The degenerate cases are therefore instances of the general theorem; the
file proves no separate lemmas about them. When `d = 0` there is exactly one
label, the empty tuple. Its block is the empty intersection `⊤`, and
`Lattice 0 = Multiplicative (Fin 0 → ℤ)` has only its identity point, which
acts as the identity. When `V = 0` every block is `⊥`, so the support set is
empty.

## Setup

Fix `d`, a finite-dimensional complex space `V` and the tuple `A`. Write
`f i` for the endomorphism underlying the unit `A.1 i`. For a complex
label `χ : Fin d → ℂ` let `W' χ = ⨅ i, (f i).maxGenEigenspace (χ i)`. The
statement's block for `c : Fin d → ℂˣ` is `W c = W' (fun i => (c i : ℂ))`.

The entries pairwise commute: for `i = j` by reflexivity, and for `i ≠ j`
by mapping the commutation `A.2` of the units through the coercion
homomorphism `Units.coeHom`.

## Independence

Commuting endomorphisms preserve each other's maximal generalized
eigenspaces (`Module.End.mapsTo_maxGenEigenspace_of_comm`). Hence
`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo` gives
`iSupIndep W'` over all complex labels. The map sending a unit tuple to its
tuple of underlying complex numbers is injective (`Units.ext`), so
`iSupIndep.comp` gives `iSupIndep W`.

## Spanning

Over the algebraically closed field `ℂ` (the instance comes from
`Mathlib.Analysis.Complex.Polynomial.Basic`), each finite-dimensional `f i`
has `⨆ μ, (f i).maxGenEigenspace μ = ⊤`
(`Module.End.iSup_maxGenEigenspace_eq_top`). With pairwise commutation,
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
gives `⨆ χ, W' χ = ⊤`.

To restrict to unit labels, it suffices to show `W' χ ≤ ⨆ c, W c` for every
complex `χ`. If every `χ i` is nonzero, `W' χ` is the block of the unit
tuple `fun i => Units.mk0 (χ i) _` and lies under the supremum. Otherwise
some `χ i = 0`. A vector `x` of `W' χ` then lies in the maximal generalized
eigenspace of `f i` for `0`, so `(f i ^ k) x = 0` for some `k`. Since
`f i` is a unit, `f i ^ k` is a unit and hence injective
(`Module.End.isUnit_iff`), so `x = 0`. Thus `W' χ = ⊥` in that case.

## Finite support

`Submodule.finite_ne_bot_of_iSupIndep` turns independence in the
finite-dimensional (hence Noetherian) space `V` into finiteness of the set
of labels with nonzero block.

## Lattice invariance

Let `ρ = Langlands.IntegerLattice.tupleRepresentationEquiv d V A`. The
lattice is commutative, so `generator d i` commutes with every `m`, and
mapping this through `ρ` and rewriting with
`Langlands.IntegerLattice.tupleRepresentationEquiv_generator` shows that
`f i` commutes with `ρ m`. Again by
`Module.End.mapsTo_maxGenEigenspace_of_comm`, `ρ m` maps each
`(f i).maxGenEigenspace (c i)` into itself, hence maps the intersection
`W c` into itself. This holds for every lattice point, including `m⁻¹`.
Because `ρ` is a monoid homomorphism, `ρ m⁻¹` and `ρ m` are mutually
inverse. `Set.InvOn.bijOn` with these two maps-to facts gives
`Set.BijOn (ρ n) (W c) (W c)` for every `n` in the full integer lattice.

## Imports and axioms

Besides the statement module, the file imports
`Mathlib.LinearAlgebra.Eigenspace.Pi` (simultaneous independence and
spanning), `Mathlib.RingTheory.Noetherian.Basic` (finite support from
independence) and `Mathlib.Analysis.Complex.Polynomial.Basic`
(algebraic closure of `ℂ`). The theorem uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

This proves only the decomposition. The common triangular basis, the
identification of the support with the common eigenvalue tuples, the
scalar-times-unipotent formulas, the commutation and nilpotence of the
unipotent parts and their multivariable product factorization remain
separate obligations of the whole-book program.
