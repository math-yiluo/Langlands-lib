# Proof: connected invariant subgroups containing torus fixed points

`Langlands.GroupScheme.Torus.solvableFixedContainmentConnected` proves
`Torus.SolvableFixedContainmentConnectedStatement.{u}` at every universe `u`. Its type is
exactly the published proposition.

Let `k : Type u` be any field and `H` a smooth connected affine group scheme over `Spec k` with
`RelativeRoot.IsSolvableScheme H`. Let a split torus `S` act on `H` by the automorphic action
`c`. Let `F` be a `c`-stable subgroup functor with `c.fixedSubgroup ≤ F`, represented by a
closed subgroup `q : C ⟶ H` with `C` smooth. Then `C` is connected. No perfectness,
characteristic, algebraic-closure or positive-rank hypothesis is used.

## Proof

The proof composes two results.

1. **Reduction to algebraically closed fields.**
   `solvableFixedContainmentConnected_of_algClosed` (module
   `Torus.SolvableFixedContainmentConnectedReduction`, by Worker 633) derives the statement
   from `SolvableFixedContainmentConnectedAlgClosedStatement`, which is the same statement with
   `[IsAlgClosed k]` added. Every hypothesis is base-changed along
   `toAlgebraicClosure k`. Containment of the fixed subgroup is transported by
   `AutomorphicAction.fixedSubgroup_baseChange`. Connectedness descends along the surjective
   projection from the base-changed representative.
2. **The algebraically closed case.** `connectedSpace_of_isAlgClosed` (module
   `Torus.SolvableFixedAlgClosedCore`) proves that statement. A generic cocharacter replaces the
   torus without changing the fixed subgroup. The published Lie–Kolchin theorem embeds
   `H ⋊ 𝔾_m` in the upper triangular group, and the acting cocharacter is made diagonal by an
   upper triangular matrix (`Dynamic.GeneralLinearTriangularDiagonal`). Every rational point of
   `C ⋊ 𝔾_m` then has unit cell minor, so it factors in the opposite cell
   (`Dynamic.TriangularCell`). The factors lie in the identity component of `C`: the
   identity-limit factor directly, and the parabolic factor through its fixed limit. The fixed
   limit lies in the image of the connected centralizer of `H ⋊ 𝔾_m` (published
   `dynamicConnected`). By the Jacobson property, a group whose rational points all lie in the
   identity component is connected. Details are in that module's Markdown.

The final theorem is `solvableFixedContainmentConnected_of_algClosed` applied to
`fun _ _ _ => connectedSpace_of_isAlgClosed`. The hypotheses of `connectedSpace_of_isAlgClosed`
are explicit arguments in the order of the algebraically closed statement.

The all-test solvability hypothesis of the statement is related to the geometric solvability
needed by Lie–Kolchin inside step 2. All-test solvability of `H ⋊ 𝔾_m` follows from
`RelativeRoot.isSolvableScheme_semidirect` and the commutativity of `𝔾_m`. Then the published
`RelativeRoot.IsSolvableScheme.isSolvableGroupScheme` gives geometric solvability.

## Source

The statement is derived from Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd edition
(2015), Proposition 2.1.12(2),(3), printed pp.59–61 (PDF pp.85–87), source
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. The implemented route
differs from the source's induction on the derived series, as explained in
`Torus/SolvableFixedAlgClosedCore.md`.

## Supporting modules

* `Langlands.GroupScheme.Dynamic.TriangularCell` (Worker 1533)
* `Langlands.GroupScheme.Dynamic.GeneralLinearTriangularDiagonal` (Worker 1533)
* `Langlands.GroupScheme.Torus.SolvableFixedAlgClosedCore` (Worker 1533)
* `Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedReduction` (Worker 633)
