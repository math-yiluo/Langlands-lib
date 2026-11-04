# Smooth representatives of actual semisimple Lie-element centralizers

This internal supporting construction by Worker 1296 combines the imported
closed representability, actual conjugation quotient and geometric coefficient
constructions. It supplies an actual chosen centralizer representative and
proves its smoothness for representation-semisimple Lie elements. It also proves
smoothness of every closed representative of the same all-test functor.
The Cartan-generation theorem remains open.

Let `k : Type u` be any field and let `G` be an actual affine group scheme over
`Spec k`. Initially assume only that `G` is locally of finite type.
`elementCentralizerGroup G X` chooses a group scheme from
`elementCentralizer_isClosedRepresentable G X`, and
`elementCentralizerGroupι G X` chooses its closed inclusion into `G`.
The two specification lemmas state that this inclusion represents the original
`elementCentralizer G X` on every test scheme and is a closed subgroup.
The representative is affine because its inclusion is closed and `G` is
affine. No smoothness, connectedness or semisimplicity hypothesis enters this
choice.

Now assume that `G` is smooth, and let `X` satisfy the published
representation-tested geometric predicate `IsSemisimpleElement G X`.
`smooth_elementCentralizerQuotient_of_isSemisimple` proves that the spectrum
of the conjugation-image quotient algebra is smooth over `k`. The proof first
transfers smoothness of `G` across its coordinate isomorphism to smoothness of
`coordinateAlgebra G` over `k`. It rewrites the actual conjugation ideal as the
image ideal of `conjugationDerivation G X`.

The theorem in `Lie.ConjugationGeometric` provides spanning eigenspaces for
this derivation after extension to `AlgebraicClosure k`.
The theorem
`SemisimpleDerivation.smooth_quotient_imageIdeal_of_eigenBaseChange`
then descends smoothness of the image-ideal quotient to `k`. Its imported
proof uses the eigenspace grading to obtain a smooth quotient after extension,
the tensor-quotient comparison, and faithfully flat smooth descent.
Faithful flatness of the algebraic closure is supplied by Mathlib's instance
for an integral domain extension that is flat and has faithful scalar action.
The affine spectrum smoothness equivalence gives the asserted scheme result.

`smooth_elementCentralizer_of_isSemisimple` applies to any actual group
scheme `C` and any closed inclusion `j : C ⟶ G` representing the original
all-test centralizer. The imported quotient comparison gives an isomorphism
over `Spec k` from `C.X` to the quotient spectrum. Transport of smoothness
through that isomorphism proves that `C` is smooth. No prior affineness,
smoothness or reducedness assumption on `C` is used.

`smooth_elementCentralizerGroup` specializes this result to the chosen
representative and its closed inclusion. Finally,
`semisimpleCentralizerSmooth` has exactly the universe-general type
`SemisimpleCentralizerSmoothStatement.{u}`. It applies the stronger
arbitrary-field result above to the smooth connected affine group quantified
in that proposition. Connectedness is unused in the stronger result.

All characteristics, imperfect and finite fields, and dimension zero are
retained. The derivation, centralizer and quotient are the imported actual
constructions, including their equations on arbitrary commutative test
algebras and their all-scheme representability. This unit is derived from
those constructions and smooth descent; it assumes no new external
structural assertion.
