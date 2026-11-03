# Split unipotence for split torus actions without zero Lie weights

Authors: Worker 1389 wrote this file (the assembly and the two transport lemmas below) and
the Hopf-level core `Langlands.Algebra.GradedHopf.*`. The proof also uses:

- Worker 1419's `𝔾ₐ`-quotient step (`Langlands.GroupScheme.HopfPrimitiveQuotient`) and
  unitriangular matrix coefficients (`Langlands.Algebra.GradedHopf.UnipotentFlag`);
- Worker 1324's grading from the torus action
  (`Langlands.GroupScheme.Rational.TorusHopfGradingAdapter`). That grading is built on the
  coordinate infrastructure `Rational/TorusUnipotence/*` of Workers 1285, 1388 and 1398, and on
  Worker 1285's `Rational/HopfCoordinateComparison`.

This file proves `TorusActionSplitUnipotenceStatement.{u}`
(`Langlands/GroupScheme/Rational/TorusUnipotenceStatement.lean`), the splitness part of CGP
Lemma 3.3.8. The theorem is `Langlands.GroupScheme.RelativeRoot.torusActionSplitUnipotence`.

The statement: let `k` be a field and `H` a group scheme over `Spec k` such that

- the structure morphism `H.X.hom` is smooth and affine;
- the underlying space `H.X.left` is connected;
- `H` is unipotent in the Library's sense (`IsUnipotent H`: every finite-dimensional matrix
  representation over a nonempty finite index type has a nonzero fixed vector).

Let `S` be a split torus over `k` acting on `H` by `b : AutomorphicAction S.toGrp H`, with
trivial zero weight space on the Lie algebra (`actionWeightSpace b 0 = ⊥`). Then
`IsSplitUnipotent H`. That is, for some `n` there is a series `HasSplitSeries n H`: a chain
`H = K₀ ⊇ K₁ ⊇ ⋯ ⊇ Kₙ`. Each `Kᵢ₊₁` is a smooth, connected closed subgroup of `Kᵢ`, normal in
`Kᵢ`, and the fppf quotient of `Kᵢ` by it is a one-dimensional vector group
(`IsVectorGroupOfDimension V 1`). The last group `Kₙ` is trivial on all tests.

## Transport lemmas

- `smooth_hom_of_iso e h`: let `e : H ≅ H'` be an isomorphism of group schemes over `Spec k`.
  If `H'.X.hom` is smooth, so is `H.X.hom`. The underlying scheme map `e.hom.hom.hom.left` is
  an isomorphism. Over `Spec k` it commutes with the structure morphisms (`Over.w`), so
  `H.X.hom` is that isomorphism followed by the smooth morphism `H'.X.hom`.
- `connectedSpace_left_of_iso e h`: if `H'.X.left` is connected, so is `H.X.left`. It is the
  continuous surjective image of `H'.X.left` under the homeomorphism `Scheme.homeoOfIso` of the
  inverse map `e.inv.hom.hom.left`.

## The proof of `torusActionSplitUnipotence`

The `IsAffineHom H.X.hom` hypothesis gives `IsAffine H.X.left` (`isAffine_of_isAffineHom`).
That is what the Library's coordinate Hopf algebra `A = AffineCoordinates.hopfAlgebra H`
needs. Let `e = AffineCoordinates.hopfSpecIso H : hopfSpec A ≅ H`.

1. Worker 1324's `TorusGradedHopf.exists_graded_of_noZeroWeight` turns `hSmooth`, the split
   torus, the action `b` and `actionWeightSpace b 0 = ⊥` into the following data. There is a
   `ℤ`-grading `𝒜` of `A` (a `GradedAlgebra 𝒜`) compatible with the bialgebra structure
   (`IsGradedBialgebra 𝒜`: the comultiplication maps degree `n` into total degree `n` of
   `A ⊗ A`, and the counit vanishes in nonzero degrees). Every degree-`0` element of the
   augmentation ideal `ker ε` lies in `(ker ε)²`.
2. `smooth_hom_of_iso e` and `connectedSpace_left_of_iso e` give smoothness and connectedness of
   `hopfSpec A`. The Library's `IsUnipotent.of_iso e` gives its unipotence.
   `smooth_hopfSpec_iff` (from `GradedHopf.SplitUnipotent`) makes `A` a smooth `k`-algebra, so
   `A` is of finite type over `k`.
3. Worker 1419's `exists_unitriangular_of_isUnipotent` applies to `A`, `𝒜` and the unipotence
   of `hopfSpec A`. It gives `G : GradedMatrixCoefficients 𝒜` with `G.M i i = 1` for all `i` and
   `G.M i j = 0` for `j < i`. These are homogeneous generators of `A` arranged in a
   multiplicative, upper unitriangular matrix.
4. The Hopf-level core `isSplitUnipotent_of_graded` takes `𝒜`, the degree-`0` condition, `G`,
   and the smoothness and connectedness of `hopfSpec A`. It gives
   `IsSplitUnipotent (hopfSpec A)`. The Library's `IsSplitUnipotent.of_iso e` then gives
   `IsSplitUnipotent H`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
