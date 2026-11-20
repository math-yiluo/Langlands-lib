# Quasi-split inner forms over semilocal rings

`Langlands.GroupScheme.reductiveSemilocalQuasiSplitInnerForm` proves
`ReductiveSemilocalQuasiSplitInnerFormStatement.{u}` for every universe `u`.
For a reductive group over the spectrum of any commutative ring with finitely
many maximal ideals, the theorem gives a quasi-split étale inner form and an
isomorphism over the base between any two such forms. Inner discrepancy is
measured by the full-centre quotient and compatible action supplied in the
published statement. [Target statement](SemilocalQuasiSplitInnerFormStatement.md)

The proof applies
`reductiveSemilocalQuasiSplitInnerFormStatement_of_geometricPrerequisites`
to four published theorems. [Assembly](SemilocalInnerFormAssembly.md)

- `relativeQuasiSplitInnerFormExistence` supplies the quasi-split inner form,
  with a Borel containing a fibrewise maximal torus. [Model proof](RelativeQuasiSplitInnerFormProof.md)
- `relativeAdjointQuotientExistence` supplies the affine fppf quotient of that
  form by its full scheme-theoretic centre. [Quotient proof](../Adjoint/RelativeExistenceProof.md)
- `relativeUnipotentRadicalFiltration` gives a finite series with additive
  vector-bundle quotients for the model Borel's unipotent radical. [Filtration proof](../RelativeUnipotent/RadicalFiltrationProof.md)
- `relativeBorelAdjointTorusWeilPresentation` identifies the image of the
  chosen maximal torus in the adjoint quotient with a Weil restriction
  of `G_m` along a finite étale algebra. [Torus proof](../RelativeLevi/AdjointTorusWeilPresentationProof.md)

For uniqueness, the assembly compares each given form with the chosen model.
It refines and conjugates the local isomorphisms so that they preserve the
Borels. The resulting discrepancy cocycles take values in the image of
the model Borel in the adjoint quotient. Its sectioned extension has the
original unipotent radical as kernel and the Weil-restricted torus as
quotient. The radical filtration and triviality of the Picard group of the
finite coefficient algebra trivialize each cocycle. The corrected local
isomorphisms descend, and their composition through the model compares the
two forms. [Borel descent](../RelativeLevi/BorelSectionedInnerDescent.md)

The source is Brian Conrad, *Reductive group schemes* (2014), Proposition
7.2.12 and its proof, pp. 258–259, and Remark 7.2.13, p. 259. The Lean
assembly implements the argument using cocycles on affine fppf refinements
and descent of the corrected isomorphisms. The original source is registered
as `conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
