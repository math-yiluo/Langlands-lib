# Semisimple matrix representations and their rational-point representations

This module is internal supporting work for the proof of
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement`
(Milne, *Algebraic Groups* (2017), Corollaries 22.43 and 22.44). It names the semisimplicity
predicate used in that statement and compares it, over an algebraically closed field, with
semisimplicity of the representation of the abstract group of rational points. The assembled
conditional reduction of that statement is the theorem
`SemisimpleIdentityComponent.charZeroSemisimpleRepresentationIdentityComponent_of` in the sibling
module `Reduction` (see `Reduction.md`).

Throughout, `k : Type u` is a field, `G` is a group scheme over `Spec k`, `n` is a finite index
type with decidable equality and `ρ : MatrixRepresentation G n`.

## The semisimplicity predicate

`MatrixRepresentation.IsSemisimpleStable ρ` abbreviates the published
`MatrixRepresentation.IsSemisimple ρ`. Its unfolded proposition is

```text
sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
  ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
```

It is, word for word, the body of the local abbreviation `IsSemisimpleRep` in the target
statement (and in `CharZeroReductiveSemisimpleRepresentationStatement` and
`SemisimpleRepresentationFieldExtensionStatement`): the coordinate space is the sum of its simple
stable subspaces. This is Milne's Definition 4.15 (printed p. 90) for the representation on
`k^n`. `simpleStableSet ρ` is the set inside the supremum.

## Stable subspaces are invariant under rational points

`IsStableCoordinates.rationalMatrix_mul` evaluates the published split-coordinate stability
equation (`IsStableCoordinates B C`) at a rational point and transports it through the canonical
isomorphism `Γ(Spec k, ⊤) ≅ k`: `ρ(g) B = B (C ρ(g) B)` over `k`.

`IsStableSubspace.rationalRepresentation_mem` (assuming `[IsAffineHom G.X.hom]`) proves that a
stable subspace `W` is invariant under `ρ.rationalRepresentation g` for every rational point `g`.
The proof applies `IsStableSubspace.rationalMatrix_mulVec_mem` and the evaluation formula
for the rational representation.

## The converse over an algebraically closed field

`isStableSubspace_of_rationalRepresentation` assumes `[IsAlgClosed k]`, `[IsReduced G.X.left]`
and `[LocallyOfFiniteType G.X.hom]`. If `W` is invariant under all rational points, then `W` is
stable in the all-test sense. The proof applies `isStableSubspace_of_rationalMatrix` after
identifying the rational action with multiplication by its matrix.

## Comparison of the two semisimplicity notions

Write `Γ` for the group `Over.mk (𝟙 (Spec k)) ⟶ G.X` of rational points and `τ` for
`ρ.rationalRepresentation`. Mathlib's `Representation.IsSemisimpleRepresentation τ` is
equivalent to `IsSemisimpleModule k[Γ] τ.asModule`.

- `submoduleOfModule ρ m` is the subspace of `n → k` underlying a `k[Γ]`-submodule `m` of
  `τ.asModule` (through Mathlib's `Subrepresentation.ofSubmodule'`); `mem_submoduleOfModule`
  says membership is unchanged. `submoduleOfModule_le_iff`, `submoduleOfModule_injective`,
  `submoduleOfModule_bot` and `submoduleOfModule_top` say it is an order embedding preserving
  `⊥` and `⊤`.
- `moduleOfStable ρ W hW` is the `k[Γ]`-submodule carried by a stable subspace `W`
  (`[IsAffineHom G.X.hom]`), and `submoduleOfModule_moduleOfStable` recovers `W`.
- `isStableSubspace_submoduleOfModule` (algebraically closed, reduced, locally of finite type):
  every `submoduleOfModule ρ m` is stable. So the image of `submoduleOfModule ρ` is exactly the
  set of stable subspaces.
- `sSup_rationalRepresentation_mem`: a supremum of rational-point invariant subspaces is
  invariant. With it, `submoduleOfModule_sSup` proves that `submoduleOfModule ρ` preserves
  arbitrary suprema.
- `isAtom_iff_submoduleOfModule_mem` and `simpleStableSet_eq_image`: the simple stable subspaces
  are exactly the images of the atoms of the submodule lattice.
- `isSemisimpleStable_iff_rationalRepresentation` (assuming `[IsAffineHom G.X.hom]`,
  `[IsAlgClosed k]`, `[IsReduced G.X.left]`, `[LocallyOfFiniteType G.X.hom]`):

  ```text
  ρ.IsSemisimpleStable ↔ ρ.rationalRepresentation.IsSemisimpleRepresentation
  ```

  The proof combines the previous items with Mathlib's `isSimpleModule_iff_isAtom`,
  `IsSemisimpleModule.sSup_simples_eq_top` and `IsSemisimpleModule.of_sSup_simples_eq_top`.

## Provenance

Internal and derived. The predicate `IsSemisimpleStable` is the encoding of Milne's
Definition 4.15 already used verbatim in the published target statement; the comparison results
are formal consequences of the published stable-subspace and rational-coordinate interfaces and
of Mathlib's semisimple-module theory. Source: J. S. Milne, *Algebraic Groups* (2017), registered
as `milne-2017-algebraic-groups`, Definition 4.15, printed p. 90 (PDF p. 106).
