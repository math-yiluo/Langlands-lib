# Maximal split tori of a derived subgroup inside an ambient maximal split torus

Author: Worker 4283.

The theorem `Langlands.GroupScheme.derivedMaximalSplitTorus` proves the
published proposition `DerivedMaximalSplitTorusStatement.{u}` from
[`Derived.MaximalSplitTorusStatement`](MaximalSplitTorusStatement.md). Its
type is exactly that proposition, at an arbitrary universe `u`.

## What is proved

Write `Spec k` for `Spec (CommRingCat.of k)`. Let `k : Type u` be any field.
It may be finite, imperfect or of positive characteristic. Let `G` and `D`
be group schemes over `Spec k` with `IsConnectedReductive G`, and let
`d : D ⟶ G` satisfy `IsDerivedSubgroup d`. Let `S` be a commutative group
scheme over `Spec k` and let `i : S.toGrp ⟶ G` satisfy
`IsMaximalSplitTorus i`. The theorem gives:

- a commutative group scheme `S_D` over `Spec k`;
- a homomorphism `j : S_D.toGrp ⟶ D` with `IsMaximalSplitTorus j`;
- a homomorphism of commutative group schemes `e : S_D ⟶ S` such that
  `CommGroupScheme.groupHom e` is a closed subgroup.

These satisfy `j ≫ d = CommGroupScheme.groupHom e ≫ i` as actual
homomorphisms on all test schemes.

The theorem does not say that `S_D` is the intersection `(S ∩ D)⁰_red`. It
does not say that `e` is surjective or that `S` lies in `D`. For example, the
diagonal torus of `GL_n` has dimension `n`, while a maximal split torus of
`D = SL_n` has dimension `n - 1`.

## The Lean proof

The proof is a single term. It applies a published reduction to a published
theorem.

1. `smoothMaximalSplitTorusConjugacy`, from
   [`Rational.SmoothMaximalSplitTorusConjugacyProof`](../Rational/SmoothMaximalSplitTorusConjugacyProof.md),
   proves `SmoothMaximalSplitTorusConjugacyStatement.{u}`. This is the
   Borel–Tits theorem (CGP Theorem C.2.3): over every field, any two maximal
   split tori of a smooth connected affine group are conjugate by a rational
   point. Its published proof has no premises.
2. `derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy`, from
   [`Derived.MaximalSplitTorusConjugacyReduction`](MaximalSplitTorusConjugacyReduction.md),
   proves `DerivedMaximalSplitTorusStatement.{u}` from that conjugacy
   statement. Applying it to step 1 gives the theorem.

The reduction in step 2 works as follows. Its paired Markdown has the full
argument.

- It reads off smoothness, affineness and connectedness of `G` from
  `IsConnectedReductive G`. These are the hypotheses of the conjugacy
  statement, so conjugacy holds for maximal split tori of `G`.
- `d` is a closed immersion, so `D` is affine and locally of finite type
  over `k`. The reduction picks a maximal split torus `j₀ : T.toGrp ⟶ D`
  with `exists_maximalSplitTorus`.
- `j₀ ≫ d` is a closed split subtorus of `G`.
  `exists_maximalSplitTorus_extension` extends it to a maximal split torus
  `m : M.toGrp ⟶ G` with `f ≫ m = j₀ ≫ d`.
- Conjugacy gives a rational point `g` of `G` and an isomorphism
  `c : M.toGrp ≅ S.toGrp` with `m ≫ (G.innerIso g).hom = c.hom ≫ i`.
- `d` represents `derivedSubgroup G`, which is normal. So conjugation by `g`
  restricts to an automorphism `φ` of `D` with
  `φ.hom ≫ d = d ≫ (G.innerIso g).hom`.
- It takes `S_D := T`, `j := j₀ ≫ φ.hom` and `e := f ≫ c.hom`, viewed as a
  homomorphism of commutative group schemes. `j` is maximal by
  `IsMaximalSplitTorus.comp_iso`. The compatibility
  `j ≫ d = CommGroupScheme.groupHom e ≫ i` follows from the three equations
  above.
- `j ≫ d` is a closed subgroup of `G`, and `i` is a closed subgroup. So
  `IsClosedSubgroup.of_comp` makes `CommGroupScheme.groupHom e` a closed
  subgroup.

## Scope and provenance

The theorem has no hypotheses beyond those of the published statement. It
adds no condition on `k` such as perfectness or a characteristic
restriction. It adds no semisimplicity of `G`, no given maximal split torus
of `D` and no assumption that `S` lies in `D`. It uses no unproved published
statement as a premise: the conjugacy input is the published proof
`smoothMaximalSplitTorusConjugacy`.

This module is an internal composition of published Library theorems. It
adds no new mathematical assertion and no new source citation. The proof
route goes through rational conjugacy of maximal split tori, as in the
context of proof task `45bba50f-b29d-49c2-b923-64037208e2e1`. It is not the
route of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Theorem C.2.15, Step 1 (printed p.604), which uses Remark C.2.12(2)
and maximal tori. The source provenance of the target is in the statement's
Markdown, and that of each input in its own paired Markdown.
