# Picard classes of invertible modules and twists

Authors: Worker 22.

Worker 22 wrote this helper module for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It is the first module of
the proof of `PicardHilbertPiecesRepresentabilityReductionStatement`; the
main theorem and the full route are in
`PicardHilbertPiecesRepresentabilityReductionProof.md`. All declarations are
in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`.

Provenance: internal. These are standard facts about the Picard group of a
scheme, stated in the form the proof needs. No literature result is
formalized here.

## Contents

For a scheme `Y`, `Group Y` is the Library's Picard group of `Y`.

- `group_add_comm`, `group_add_left_comm`: the Picard group is commutative.
  The Library gives `Group Y` an `AddGroup` instance only. Commutativity is
  read off from the `AddCommGrpCat` object `Group.functor.obj (op Y)`.
- `icl M hM`: the class of an invertible module `M`, defined as the class of
  the line bundle `lineBundleOfIsInvertible M hM`.
- `icl_eq_iff`: two invertible modules have the same class if and only if
  they are isomorphic (`LineBundle.classOf_eq_iff`).
- `icl_lineBundle`: for a line bundle `L`, `icl L.obj _ = L.classOf`.
- `icl_tensor`: `icl (M ⊗ M') = icl M + icl M'`. Here `⊗` is the tensor
  product of the FLT port used in the statements. `portedTensorExplicitIso`
  compares it with the Library's tensor product, which `LineBundle.tensor`
  uses.
- `icl_pullback`: the class of a pullback is `Group.pullback` of the class.
- `icl_unit`: the structure sheaf has class `0`.
- `isInvertible_tensor`: tensor products of invertible modules are
  invertible (`IsInvertible.tensor_monoidalV2`).
- `twist L P m`: the module `L ⊗ P ⊗ ⋯ ⊗ P` with `m` factors `P`, written
  with `Nat.rec` exactly as in `PicardHilbertPiecesRepresentabilityStatement`.
  It is an `abbrev`, so it unfolds to the form in the statements.
  `isInvertible_twist` shows it is invertible, and `icl_twist` gives
  `icl (twist L P m) = icl L + m • icl P` by induction on `m`.
- `nonempty_iso_tensor_of_icl`: if `icl M = icl M' + icl N`, then
  `M ≅ M' ⊗ N`.
- `classOf_dual`: the dual line bundle has the negative class. The proof uses
  the evaluation isomorphism `L ⊗ L^∨ ≅ O_Y`
  (`Langlands.Scheme.Modules.isIso_dualTensorEval`).
