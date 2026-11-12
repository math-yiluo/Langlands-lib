# Conjugacy of maximal split tori inside a minimal parabolic subgroup

Author: Worker 4108 (Task 4108). Worker 15 first recorded this composite
term, `minimalParabolicSplitTorusConjugacy_of_smoothConjugacy SC`, in the
public note `notes/group-schemes/smooth-split-torus-conjugacy-route.md`.
Worker 4108 put it into this module and checked it.

`Langlands.GroupScheme.minimalParabolicSplitTorusConjugacy` proves the exact
published proposition
`Langlands.GroupScheme.MinimalParabolicSplitTorusConjugacyStatement.{u}`
(module `Langlands.GroupScheme.Rational.ParabolicTorusStatement`) at an
arbitrary universe `u`.

Let `k : Type u` be any field and `G` a group scheme over
`Spec (CommRingCat.of k)` with `IsConnectedReductive G`. Let `j : P ⟶ G`
satisfy `IsMinimalParabolicSubgroup j`. Let `i : T.toGrp ⟶ G` and
`i' : T'.toGrp ⟶ G` satisfy `IsMaximalSplitTorus`, and let
`f : T.toGrp ⟶ P` and `f' : T'.toGrp ⟶ P` satisfy `f ≫ j = i` and
`f' ≫ j = i'`. Then there are a ground-field point
`p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X` and an isomorphism
`e : T.toGrp ≅ T'.toGrp` with

```lean
f ≫ (P.innerIso p).hom = e.hom ≫ f'
```

This is an equation of group scheme homomorphisms into `P` itself, so the
conjugating point lies in `P(k)`, not merely in `G(k)`. The field may be
finite or infinite, perfect or imperfect, of any characteristic. The theorem
has no hypotheses beyond those of the statement.

## Proof

The proof is one term that combines two published theorems.

1. `smoothMaximalSplitTorusConjugacy` (module
   `Rational.SmoothMaximalSplitTorusConjugacyProof`) proves
   `SmoothMaximalSplitTorusConjugacyStatement.{u}`. Over every field, any two
   maximal split tori of a smooth, affine, connected group are conjugate by a
   rational point of that group.
2. `minimalParabolicSplitTorusConjugacy_of_smoothConjugacy` (module
   `Rational.ParabolicConnectedConjugacy`) derives the target from that
   statement.

Step 2 applies the conjugacy statement to the group `P` itself. Its proof,
documented in `Rational/ParabolicConnectedConjugacy.md`, works as follows:

- `P` is smooth because it is parabolic (`IsParabolicSubgroup.smooth`).
- `P` is affine, because `j` is a closed immersion and `G` is affine.
- `P` is connected by `IsParabolicSubgroup.connectedSpace`, which uses the
  Borel subgroup over the algebraic closure.
- `f` and `f'` are maximal split tori of `P`, by
  `IsMaximalSplitTorus.of_comp`, since `j` is a closed subgroup and
  `f ≫ j = i`, `f' ≫ j = i'`. This happens inside
  `exists_innerIso_comp_eq_of_smooth_connected_closed_factorizations`.

From minimality, the reduction uses only the fact that a minimal parabolic is
parabolic (`IsMinimalParabolicSubgroup.isParabolicSubgroup`).

## Source

The statement is the conjugacy of maximal split tori inside a minimal
parabolic subgroup in Borel and Tits, *Groupes réductifs* (1965); see the
statement Markdown `Rational/ParabolicTorusStatement.md` for its source
locations. The proof here takes a different route. It is the Borel–Tits
conjugacy theorem for smooth connected affine groups, Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Theorem C.2.3, printed
p.593, applied to the group `P`. The proofs of the two published theorems are
described in their own modules.

## Dependencies

The module imports the statement module
`Langlands.GroupScheme.Rational.ParabolicTorusStatement` and the two modules
above. It does not use the relative Weyl group, the rational Bruhat
decomposition, or Tits systems. It also uses no theorem whose proof consumes
this statement.
