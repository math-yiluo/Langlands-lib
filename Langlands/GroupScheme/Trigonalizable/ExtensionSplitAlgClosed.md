# Splitting of trigonalizable extensions over algebraically closed fields

Author: Worker 60 (Task 7805). Module
`Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed`, namespace
`Langlands.GroupScheme.TrigonalizableExtensionSplit`.

This module proves case (a) of Milne's Theorem 16.26 in the encoding of the
published statement `TrigonalizableExtensionSplitStatement`, and the
existence of the character-linear kernel tower of Milne's Theorem 16.21 over
every field. It does not prove cases (b) and (c) of the statement.

## Setting

`k : Type u` is a field, `G` a group scheme over `Spec k` with
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`, `U` a group
scheme with `i : U ⟶ G`, `Λ : Type u` a finitely generated additive
commutative group and `q : G ⟶ D(Λ)`, where
`D(Λ) = (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`. The
hypotheses are those of the published statement: `IsClosedSubgroup i`,
`IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal` and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.

## Declarations

- `admitsTower`: under these hypotheses, over any field,
  `LinearKernelTower.AdmitsTower D(Λ) q`: the map `q` has a finite tower of
  fppf quotients whose actual kernels are closed subgroups of `𝔾ₐ` on which
  conjugation acts through a character of `D(Λ)` (the Library's definition in
  `LinearKernelTower`).
- `exists_section_of_isAlgClosed`: if moreover `[IsAlgClosed k]`, there is a
  group-scheme homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙`.

## Proofs

`admitsTower`: `U` is affine because `i` is a closed immersion into the affine
`G`. `exists_triangular_embedding` gives a closed `j : G ⟶ B_N` whose diagonal
map `f = j ≫ blockLimitHom` has actual kernel range equal to `range i`. Hence
`kernelι q ≫ f = 0`, and the published `FppfHomDescent` gives `d` with
`q ≫ d = f`. Rewriting the fppf quotient hypothesis with the kernel equality
gives `RelativeRoot.IsFppfQuotient (range (kernelι f)) q`. The published
`TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient`,
with the published proofs `affineHomImage` and `affineNormalSubgroupQuotient`,
then constructs the tower (it does not need `d` to be a closed immersion).

`exists_section_of_isAlgClosed`: apply the published
`LinearKernelTower.sectionExistence` (homomorphic sections of towers over
algebraically closed fields, through Milne 15.34(d)) to the tower.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, printed
pages (PDF page = printed page + 16):

- Theorem 16.26, p.332: "The extension e → G_u → G → D → e splits in each of
  the following cases: (a) the field k is algebraically closed; ..."
- Proof of Theorem 16.26, pp.332–333, which uses the normal series of
  Theorem 16.21, p.330, pulls back along a section of `G/N → D`, and in case
  (a) applies Theorem 15.34(d).

The correspondence between Milne's statement and the hypotheses on `i` and
`q` is recorded in the paired Markdown of the published statement
`Langlands/GroupScheme/Trigonalizable/ExtensionSplitStatement.md`. This
module's case (a) theorem has exactly those hypotheses, with the disjunction of
cases replaced by `[IsAlgClosed k]`. The implemented route is Milne's: the
tower is built from a triangular embedding (16.2, 16.21) and split step by
step by the published tower theorem.
