# Proof of the classification of Picard-zero line bundles

Module `Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof`
proves `Langlands.AbelianScheme.PicardZeroLineBundleClassificationStatement`
with no hypotheses.

## Main theorem

`Langlands.AbelianScheme.picardZeroLineBundleClassification :
PicardZeroLineBundleClassificationStatement.{u}`.

The statement says the following. Assume `preservation`, that the pullback
tensor comparison maps are isomorphisms. Let `A` be an abelian scheme over
`S` with a chosen dual scheme `hA`, let `T` be a scheme over `S`, and let
`N` be a line bundle on `T ×_S A`. Assume that `N`, transported to the base
change `A_T` along `relativeSpaceSymmetry`, is geometrically Picard-zero.
Then there is a morphism `φ : T ⟶ dualScheme A hA` over `S` such that `N`
is isomorphic to `P_φ ⊗ pr_T^* (e_T^* N)`. Here `P_φ` is the underlying
bundle of the relative pullback of the Poincaré family along `φ`, `pr_T` is
the projection to `T`, and `e_T` is the unit section over `T`. The
statement Markdown gives the exact form.

## Proof

The theorem applies
`picardZeroLineBundleClassification_of_inverse` (module
`PicardZeroLineBundleClassificationFromInverse`) to
`Langlands.AlgebraicGeometry.Picard.LineBundle.exists_tensorObj_iso_structureSheaf`
(module `LineBundleDualEvaluation`). The first result derives the
classification from the hypothesis that every line bundle `L` has a line
bundle `M` with `L ⊗ M ≅ O_X`. The second result proves that hypothesis,
with `M` the dual of `L`. So the proof is a single term with no further
steps.

## Provenance

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
Chapter VI, (6.2)(ii); see the Markdown of
`PicardZeroLineBundleClassificationStatement`. The two imported modules
document the steps of the proof. Worker 266 wrote
`PicardZeroLineBundleClassificationFromInverse`, and Worker 270 wrote
`LineBundleDualEvaluation` and this module.
