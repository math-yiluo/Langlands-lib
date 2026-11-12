# Regular representations and the smooth tensor–Hom theorems

Author: Worker 139.

`Langlands.Renard.Smooth.renardTensorHomStatements` has exactly the published
type `Langlands.Renard.Smooth.RenardTensorHomStatements`, with independent
group and representation-carrier universe parameters. Its statement pair and
all files imported by that statement remain unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition of 9 July 2026, III.1.2–III.1.3 (printed pp.58–59 / PDF
pp.64–65) and III.1.15 (printed pp.67–70 / PDF pp.73–76); registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The theorem assembles the following four exact component proofs:

1. `regularRepresentationSmooth` and `leftRegularHeckeAction`, from
   `RenardRegularHeckeProof`, prove smoothness of the left and right regular
   representations and identify the integrated left Hecke action with
   convolution. Their paired Markdown explains the compact open subgroup and
   scalar integral arguments.
2. `tensorHomAdjunction`, from `RenardTensorHomAdjunctionProof`, proves the
   smooth-value lemma, the equivalence of smooth Hom representations with the
   prescribed currying formula, and the resulting linear equivalence of
   intertwiner spaces. Its paired Markdown explains the restriction of
   equivariant currying to smooth parts.
3. `tensorHomExactness`, from `RenardTensorHomExactnessProof`, proves both
   smooth Hom exactness assertions and all three projective or injective
   preservation assertions. Its paired Markdown explains compact-group
   splittings, the adjunction, transposition and tensor injectivity over ℂ.

The final proof is a conjunction constructor. None of its conclusions is
conditional on a further statement. The compact semisimplicity step reuses the
published stronger compact-coefficient theorem specialized to a compact domain;
it does not depend on an unpublished IV.1.1 proof. All actual representations,
Hecke action, smooth submodules and intertwiner spaces are those named by the
published statement.
