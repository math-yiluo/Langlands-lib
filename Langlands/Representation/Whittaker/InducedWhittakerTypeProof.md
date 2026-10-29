# Whittaker type of upper block induction

Author: Worker 174.

The theorem `Langlands.inducedWhittakerType.{uF,uV}` proves exactly the closed
proposition `Langlands.InducedWhittakerTypeStatement.{uF,uV}` from
`InducedStatement`. The proof applies the published theorem
`Langlands.inducedWhittakerTypeReduction` to the published closed theorem
`Langlands.inducedLocalization`. No geometric premise remains in the result.

For every prime, canonical p-adic field, positive total rank and ordered block
shape, and every family of admissible complex block representations of finite
type, the actual upper unnormalized smooth induction has a nonzero equivariant
linear functional spanning all such functionals if and only if each block
representation has one. The statement retains every continuous, nontrivial,
unitary raw additive character. Its covariance uses the actual
upper-unitriangular matrices and the explicit double product of character
values on adjacent matrix entries. The field universe `uF` and block-module
universe `uV` are independent.

## Implemented proof

The Lean term supplies
`inducedLocalization.{uF,uV} : InducedLocalizationStatement.{uF,uV}` to
`inducedWhittakerTypeReduction.{uF,uV}`. The latter proves
`InducedLocalizationStatement.{uF,uV} →
  InducedWhittakerTypeStatement.{uF,uV}`. Thus the conclusion is the original
closed functional-space proposition with all its hypotheses and both
directions of its equivalence.

The imported [localization proof](InducedLocalizationProof.md), by Worker 330,
identifies the actual induced character quotient with the tensor of the block
character quotients. Its geometric assembly uses the upper-unipotent support
filtration, vanishing of all nonselected character quotients, and the open
stabilizer comparison. The open stabilizer comparison handles the block
reversal and positive character explicitly and returns the block quotients in
their original order. This theorem works directly with upper unnormalized
induction.

The imported [algebraic reduction](InducedWhittakerTypeReductionProof.md), by
Worker 174, first rewrites the target's explicit covariance as membership in
the actual Whittaker functional submodules. Existence of a nonzero functional
spanning such a submodule is equivalent to its dimension being one.
`Whittaker.functionalsLocalizationDualEquiv` identifies each functional
submodule with the full dual of its character quotient.
`LinearAlgebra.dual_finrank_one_iff` reflects dimension one to that quotient,
the localization equivalence preserves dimension, and
`LinearAlgebra.piTensor_finrank_one_iff` identifies dimension one of the tensor
with dimension one of every block quotient. The dual translations then
recover the block functional conditions.

These imported arguments preserve both nonzero existence and uniqueness up
to scalar. They require no finite-dimensionality hypothesis on the block
modules or their quotients and make no identification of an unrestricted
tensor dual with a tensor product of duals. Reducible representations and zero
modules remain within the target's quantifiers. No irreducibility or extra
nonvanishing hypothesis is introduced.

## Provenance

This module is the final internal application of the two published theorems,
whose paired documentation explains their constructions and source
relationships. It reuses them by Lean name and copies no unpublished draft.
The target Lean/Markdown pair and all of its imports are unchanged.

The original source map is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), printed pages 377 and 385–387,
registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
and Rodier's modified author manuscript, *Modèles de Whittaker des
représentations admissibles des groupes réductifs p-adiques quasi-déployés*,
Chapter V.2, Theorem 4 and Lemma 6, PDF pages 36–42, registered as
`rodier-whittaker-author-manuscript`, SHA256
`8c110b6b626108ec67421f288baa4b761a8073df2c68db6be8360b654f569812`.

JPSS states the dimension-one equivalence using normalized lower induction
and admissible finite-type blocks. Rodier's manuscript gives the geometric
heredity argument with irreducible inducing data. The imported full-quotient
theorem is a derived strengthening proved through the formal geometric
assembly; the algebraic reduction then yields the exact present target.
This final proof therefore uses that established upper unnormalized quotient
comparison rather than a separate normalization argument or an inference
from JPSS's attribution alone.
