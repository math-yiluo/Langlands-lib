# Equivalent automorphic representations have the same local components

Author: Worker 3657.

Lean module: `Langlands.Automorphic.LocalComponentDeterminationForward`. It
imports only `Langlands.Automorphic.OperatorSubquotientLocalComponentStatement`
and changes no published file.

This module proves the forward implication "⇒" of
`Langlands.Automorphic.LocalComponentDeterminationStatement` (Task 6817)
from `LocalComponentExistenceStatement` (proved by the Library's
`localComponentExistence`, Task 6815). The reverse implication "⇐" is
`localComponentDetermination_reverse` (module
`LocalComponentDeterminationReverse`), and the target is assembled in
`LocalComponentDeterminationProof`.

## Main theorem

```lean
theorem Langlands.Automorphic.localComponentDetermination_forward
    (hex : LocalComponentExistenceStatement.{u})
    (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q Q' : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible) (he : Nonempty (Q.Equivalence Q')) :
    (finite places) ∧ (real places) ∧ (complex places)
```

The conclusion is the right-hand side of the biconditional in
`LocalComponentDeterminationStatement`, copied verbatim: at every finite place
some irreducible representation `ρ` of `GL_(r+1)(F_v)` on a
`W : ModuleCat.{u} ℂ` makes both `Q` and `Q'` `ρ`-isotypic, and at every real
or complex place some irreducible `(𝔤, K)`-module `(V, ρ, π)` with
`V : ModuleCat.{u} ℂ` does. Only the joint admissibility of `Q` is used (the
target also assumes that of `Q'`).

## Proof

- `OperatorSubquotient.Equivalence.apply_representation`: an equivalence
  `e : Q.Equivalence Q'` (an equivalence of the representations of the whole
  concrete operator algebra) commutes with every operator `a`.
- Every local action in the isotypy predicates is the action of operators of
  the algebra: local translations at a finite place are finite translations
  (`finiteOperator`), the compact actions at infinite places are compact
  operators, and the place Lie actions are enveloping operators
  (`envelopingAction`, through `complexLieAction`). Hence composing with `e`
  sends intertwining maps from `ρ` into `Q` to intertwining maps into `Q'`
  (`Equivalence.localIntertwining` at a finite place; membership in
  `Archimedean.gkHoms` at an infinite place).
- `iSup_range_eq_top_of_comp` and `iSup_mem_range_eq_top_of_comp`: if the
  ranges of a family of maps into `N` span `N`, the ranges of their composites
  with a linear equivalence `e : N ≃ N'` span `N'` (the image of the span
  under `e` is the span of the images, and `e` is surjective).
- `isFinitePlaceIsotypic_of_equivalence`,
  `isRealPlaceIsotypic_of_equivalence`,
  `isComplexPlaceIsotypic_of_equivalence`: so isotypy of `Q` at a place
  transfers to `Q'`.
- `localComponentDetermination_forward`: `LocalComponentExistenceStatement`
  gives, for `Q`, an irreducible admissible component at every place. At a
  finite place it is `A : AutomorphicObject`; the theorem takes
  `W = ModuleCat.of ℂ A.obj` and `ρ = A.obj.representation`, irreducible by
  `A.property.1`. At infinite places it takes the `(𝔤, K)`-module given by
  the statement. The transport lemmas give isotypy of `Q'`.

The module activates the statement module's local instances (including the
canonical topology `localComponentGeneralLinearTopology`, needed to write
`A.obj.representation`).

## Provenance

The forward implication transports the local types along a global
isomorphism, as in the uniqueness part of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Theorem 6.3.7, pp. 165–166
(PDF pp. 179–180) (`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), and of
Flath's Theorem 3, p.181 (PDF 177) (`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`): isomorphic
representations have isomorphic local components, read through isotypic
restriction as in Flath's proof of Theorem 1, p.180 (PDF 176). The proof
follows the statement Markdown's route 3 "⇒" (transport of isotypy along the
equivalence).

## Axioms

`lean_check` (lake build) inspection 7ca29ec8 of `localComponentDetermination_forward`: only `propext`,
`Classical.choice` and `Quot.sound`. Rechecked in the lake build dbe84f71 of the full Task 6817 draft
(0 errors, 0 warnings).
