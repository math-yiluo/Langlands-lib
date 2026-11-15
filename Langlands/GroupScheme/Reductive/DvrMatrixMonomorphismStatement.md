# Reductive monomorphisms into general linear groups over a DVR

`Langlands.GroupScheme.ReductiveDvrMatrixMonomorphismStatement.{u}` is the
remaining matrix assertion in the DVR reduction of the reductive monomorphism
theorem. It says that, for every discrete valuation ring `R : Type u`, every
reductive group scheme `M` over `Spec R`, every natural number `N`, and every
actual representation `ρ : MatrixRepresentation M (Fin N)`, monicity of the
underlying scheme morphism of `ρ` implies `IsClosedSubgroup ρ`.

Here a representation is an actual homomorphism from `M` to
`GeneralLinear.groupScheme (Fin N) (CommRingCat.of R)`, and
`IsClosedSubgroup ρ` means that its underlying scheme morphism is a closed
immersion. Monicity is also imposed on that scheme morphism. No
pointwise-only condition or extra property of the generic fibre is substituted
for either condition. The statement is universe polymorphic and is defined as a
proposition; this file does not prove it.

## Conditional reductions

`DvrMatrixReduction.flatAffineCase_of_matrixCase` proves that the matrix
assertion and `DedekindLinearEmbeddingStatement` imply
`DvrAffineClosureReduction.FlatAffineCase`. Given a monomorphism `f : M → G`
with reductive source and flat affine finite-type target, the explicitly
supplied embedding assertion produces a closed representation `ρ : G → GL_N`.
The composite `f ≫ ρ`, encoded as `ρ.restrict f`, is monic. The supplied matrix
assertion makes it a closed immersion. Closed-immersion cancellation along the
separated morphism `ρ` then makes `f` a closed immersion.

`DvrMatrixReduction.dvrCase_of_matrixCase` composes that implication with
`DvrAffineClosureReduction.dvrCase_of_flatAffineCase`. Its conclusion is exactly
the published `ReductiveMonomorphismValuativeReduction.DvrCase.{u}`. Its three
explicit premises are `DvrGenericAffinenessStatement.{u}`,
`DedekindLinearEmbeddingStatement.{u}`, and the matrix assertion just defined.
Thus it includes the preceding schematic-closure reduction to a flat affine
target, with Raynaud affineness supplied as a premise.

## Source and provenance

Brian Conrad, *Reductive group schemes* (2014), proof of Theorem 5.3.5, printed
and PDF p.166, first reduces to a flat affine target using the generic image
closure and Raynaud, then embeds that target as a closed subgroup of `GL_n`
and replaces it by `GL_n`. The matrix assertion is the resulting specialization
of the theorem to that target. It is derived content rather than a separately
numbered result in the source. The two implications implement the categorical
composition and cancellation in this reduction.

The registered source is `conrad-2014-reductive-group-schemes`, retained at
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`,
with SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The cited original page was read. The embedding assertion itself is the
previously published `DedekindLinearEmbeddingStatement`, whose source is
Conrad's Exercise 5.5.7.

The file proves these conditional implications, without proving Raynaud
affineness, the embedding assertion, the matrix assertion, or the
arbitrary-base reductive monomorphism theorem. The valuative and approximation
steps remain separate obligations.
