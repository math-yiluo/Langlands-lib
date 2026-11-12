# Proper morphisms of algebraic spaces under a change of base scheme

Author: Worker 3519. Shared as a Task 5498 draft by Worker 101; checked and submitted by
Worker 182.

`properSchemeBaseChange` proves `ProperSchemeBaseChangeStatement`
(`ProperSchemeBaseChangeStatement.lean`). Let `S` and `T` be arbitrary schemes in a common
universe `u`, `g : T ⟶ S` an arbitrary morphism, `X` and `Y` algebraic spaces over `S`, and
`f : X ⟶ Y` a proper morphism. Then `baseChangeMap g f : baseChange g X ⟶ baseChange g Y` is
proper over `T`. No representability of `f` and no hypothesis on `S`, `T` or `g` is used.

## Source

The Stacks Project, *Morphisms of Algebraic Spaces*, version ed88ff78, Lemma 40.3, Tag 04WP,
printed p.81: proper morphisms are stable under base change. The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`. The Stacks proof cites the base-change
stability of the components of Definition 40.1 (Tag 03ZM, p.80): separatedness (Lemma 4.4,
Tag 03KL, p.4), finite type (Lemma 23.3, Tag 03XH, p.45) and universal closedness (Lemma 9.3,
Tag 03IS, p.15). The quasi-compact part of finite type is Lemma 8.4 (Tag 03HF, p.13).

## Implemented proof

The proof applies the published theorem `IsProperMorphism.baseChangeMap` from
`TopologicalMorphismBaseChange.lean` to the given proper morphism. That theorem has the same
generality as the statement: arbitrary schemes `S`, `T` in a common universe, an arbitrary
`g : T ⟶ S` and an arbitrary morphism `f` of algebraic spaces over `S`. It combines the
component results for the four parts of the published `IsProperMorphism`:

- separatedness and local finite type, by `IsSeparatedMorphism.baseChangeMap` and
  `IsLocallyOfFiniteTypeMorphism.baseChangeMap` from `SpaceMorphismBaseChange.lean`;
- quasi-compactness, by `IsQuasiCompactMorphism.baseChangeMap`: for an affine test scheme over
  `T`, the same scheme viewed over `S` has a compact étale surjective atlas of its fibre, and the
  same atlas scheme with its induced structure over `T` is an atlas of the fibre over `T`;
- universal closedness, by `IsUniversallyClosedMorphism.baseChangeMap`: the fibre over a test
  scheme over `T` and the same fibre viewed over `S` have homeomorphic point spaces, compatibly
  with the projections, so the closed projection over `S` gives the closed projection over `T`.

No proof step of this module goes beyond that application.

## Scope

The theorem keeps every quantifier of the statement: the universe `u`, arbitrary schemes `S` and
`T`, an arbitrary morphism `g`, arbitrary algebraic spaces `X`, `Y` over `S`, and the published
`IsProperMorphism` (separated, quasi-compact, locally of finite type, universally closed). The
imports are the unchanged statement module and `TopologicalMorphismBaseChange`.
