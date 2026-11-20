# Eventual finite type of representing objects of the projective frame charts

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartFiniteTypeStatement` is a
proposition definition. It is a statement only. The module proves nothing.

## The statement

Fix `P : Prerequisites.{0}` and natural numbers `g d` with `0 < g` and
`hd : 0 < d`. The statement says that some natural number `N` has the following
property. Let `n ≥ N` with `hn : 3 ≤ n`, and let
`ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n` be a family of
`6^g·d + 1` level coefficient tuples. Then there are a level base
`X : LevelBase n` and a natural transformation
`a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn` such that:

- each component `a.app T` is injective;
- for every level base `T` and datum `b : Datum P T.obj g d n`, the class
  `b.classOf` lies in the image of `a.app (op T)` exactly when the frame locus
  `b.frameLocus ρ` (module `FrameLocus`) is all of `T`;
- the canonical structure morphism `X.toLocalizationSpec : X.obj ⟶ Spec ℤ[1/n]`
  (module `LocalizationBase`) is locally of finite type and quasi-compact
  (Mathlib's `LocallyOfFiniteType` and `QuasiCompact`). Here `ℤ[1/n]` is
  `Localization.Away (n : ℤ)`.

The first two items are the conclusion of the published
`FrameChartRepresentabilityStatement` for the same `P g d n hd hn ρ`: the frame
chart for `ρ` is represented by `X`. The new content is the third item: the
representing level base is of finite type over `Spec ℤ[1/n]`. The statement
asserts this only for levels `n ≥ N`, with `N` depending on `P`, `g` and `d`.
The hypothesis `0 < g` matches the companion statements
`FrameLocusCoverStatement` and `LargeLevelFiniteTypeStatement`.

## Provenance

This is a derived statement. Its source is Mumford–Fogarty–Kirwan, *Geometric
Invariant Theory*, 3rd edition, registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`
(content SHA-256
`3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`), Chapter 7,
§2. There `m = 6^g·d − 1`, so a projective frame of `ℙ^m` has `m + 2 = 6^g·d + 1`
points. This matches the index type `Fin (cubicProjectiveDimension g d + 2)`,
since `cubicProjectiveDimension g d + 1 = 6^g·d` for `d > 0`.

- Proposition 7.3 (printed p.132, PDF p.145): "There is a locally closed
  subscheme `H_{g,d,n}` of `Hilb^{P,2g+1}_{ℙ^m}` such that an S-valued point of
  `Hilb^{P,2g+1}` is in the image of Φ if and only if it is an S-valued point of
  `H_{g,d,n}`. Therefore `H_{g,d,n}` represents `ℋ_{g,d,n}`." Here `ℋ_{g,d,n}` is
  the functor of linearly rigidified polarized abelian schemes with level `n`
  structure (Definitions 7.5 and 7.6, printed p.130, PDF p.143).
- Proposition 7.4 (printed p.135, PDF p.148): "The schemes `Z_{g,d,n}` and
  `H_{g,d,n}` are quasi-projective over Spec (Z) and carry PGL(m + 1) linearized
  ample invertible sheaves".

The derivation has three steps.

1. *The chart is a closed subscheme of `H_{g,d,n}`.* This identification is
   recorded in the Markdown of `FrameChartRepresentabilityStatement`. On the
   frame locus, the `m + 2` torsion sections `P_{ρ_0}, …, P_{ρ_{m+1}}` determine
   a unique linear rigidification that sends them to the standard projective
   frame. So the frame chart is represented by the closed subscheme of
   `H_{g,d,n}` where the corresponding universal sections, composed with the
   rigidified embedding into `ℙ^m × H_{g,d,n}`, are the standard frame points.
2. *Finite type over `Spec ℤ`.* By Proposition 7.4, `H_{g,d,n}` is
   quasi-projective over `Spec ℤ`. In the EGA sense this includes finite type
   (registered Stacks snapshot
   `stacks-quasi-projective-ample-finite-type-2026-11-19`, content SHA-256
   `112270b8b6f437c38228945f1221ccc306b020c84ff13bc87f6c2c6efda77692`,
   Definition 29.41.1, file `Stacks-29.41-01VV.html`: "`f` is quasi-projective if
   `f` is of finite type and there exists an `f`-relatively ample invertible
   `O_X`-module"). A closed subscheme of a scheme of finite type over `Spec ℤ` is
   of finite type over `Spec ℤ`.
3. *Finite type over `Spec ℤ[1/n]`.* A scheme `X` of finite type over `Spec ℤ`
   is quasi-compact, so its morphism to the affine scheme `Spec ℤ[1/n]` is
   quasi-compact. The morphism `X → Spec ℤ` factors through `Spec ℤ[1/n]`,
   because `n` is a unit on `H_{g,d,n}` (step (IV) of the proof of
   Proposition 7.3 restricts to residue characteristics prime to `n`). Local
   finite type passes to the first factor of a composite. Every morphism from a
   level base to `Spec ℤ[1/n]` is the canonical one
   (`LevelBase.eq_toLocalizationSpec`, module `LocalizationBase`).

The source's functor and the Library's `moduliFunctor` are compared in the
Markdown of the published target `LargeLevelQuasiProjectivityStatement`.

The steps above need no lower bound on `n` beyond `3 ≤ n`. A second derivation
explains the bound `N`. By Theorem 7.9 (printed p.139, PDF p.152), for
`n > 6^g · d · √(g!)` the fine moduli scheme `A_{g,d,n}` exists and is
quasi-projective over `Spec ℤ`. The frame chart is then an open subscheme of
`A_{g,d,n}`, namely the frame locus of the universal datum, and an open subscheme
of a noetherian scheme is quasi-compact. Either derivation gives the statement as
written. The existential bound `N` makes the statement weaker than a version for
all `n ≥ 3`.

## Role

This statement is the finiteness input of the proved definition
`largeLevelFiniteType_of_frameChartFiniteType` (module
`LargeLevelFiniteTypeChartReduction`). With the published statements
`FrameLocusBaseChangeStatement` and `FrameLocusCoverStatement`, that definition
proves `LargeLevelFiniteTypeStatement`. The published
`FrameChartRepresentabilityStatement` gives the charts but not their
quasi-compactness or local finite type, which is why this separate statement is
needed.
