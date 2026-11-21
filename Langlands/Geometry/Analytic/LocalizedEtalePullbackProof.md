# Pullbacks along étale morphisms in the localized analytic category

For any complete ultrametric normed field `K : Type u`,
`Langlands.Analytic.SaturatedAtlasPresentation.localizedEtalePullbackBaseChange`
proves the Library's `LocalizedEtalePullbackStatement.{u, v} K`. Given
localized arrows `f : A ⟶ X` and `g : B ⟶ X` with `etale f`, it supplies
`p : P ⟶ A` and `q : P ⟶ B` with `IsPullback p q f g` and `etale q`. The
pullback lies in `LocalizedCategory.{u, v, v} (K := K)` for independent `u`
and `v`. [Target statement](EtaleGeometricPointPullbacks.md)

The proof applies `localizedEtalePullback_of_targetLocality_and_finitePieces`.
For target-local finiteness, it passes `finiteAffinoidAlgebraDescent` to
`finiteOverTargetLocality_of_descent`. This glues the finite algebras of each
subordinate target refinement and recognizes the descended algebra on the
actual inverse-image locus. For the second criterion, it passes
`finitePiecesEtaleAllPieces`, which transports pointwise étaleness from the
finite neighborhood family to every recognized target piece using domain
flatness and finite tensor comparison.
[Target-local finiteness](FullRecognitionFiniteTargetLocalityOfDescent.md),
[effective descent](GeneralizedAffinoid/FiniteAffinoidAlgebraDescent/Proof.md),
[finite-to-all étaleness](FinitePiecesEtaleAllPiecesProof.md)

The assembly uses finite Banach pushouts to show that the glued quotient
admits a presentation in the original space and atlas-index universe. The two
criteria give the all-pieces étaleness certificate for its second projection.
The recognized pullback's limiting cone supplies the universal property on
full localized morphisms, and the strong-to-localized reduction transports the
square and its étale projection to the given cospan. The theorem applies to
arbitrary ambient analytic spaces in the localized category.
[Pullback assembly](ConditionalLocalizedEtalePullback.md),
[localized reduction](LocalizedEtalePullbackReduction.md)
