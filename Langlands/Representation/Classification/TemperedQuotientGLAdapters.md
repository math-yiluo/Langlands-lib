# GL adapters for the independent tempered quotient argument

This module is internal algebraic assembly for Worker 624's unfinished
proof of `Langlands.Classification.TemperedLanglandsQuotientCoverage`. It does
not assert coverage, analytic preservation under duality, or induction duality.
Its provenance is the composition of published constructions and the generic
adapter in the paired `TemperedQuotientAux` module.

`glSmoothDualQuotientMap` defines the actual map by specializing
`smoothDualPullbackToOriginal` to an irreducible smooth representation of
`GL_n(F)`. It composes contragredient pullback with the inverse of canonical
smooth bidual evaluation. The published cuspidal embedding theorem supplies
admissibility of the input, and the published compact-open cofinality theorem
supplies the separation and reflexivity hypotheses. The supplied topological
realization is arbitrary. The field, input carrier and auxiliary carrier
universes remain independent, and the resulting surjection has the original
input as its actual codomain. This elementary adapter works also in rank zero;
the final coverage target retains its positive-rank restriction.
`glSmoothDualQuotientMap_surjective` proves surjectivity of this defined map
when the auxiliary representation is smooth and the supplied map from the
input's smooth dual is nonzero. `gl_exists_surjective_from_smoothDual` returns
this map together with that proof.

`oppositeJacquet_action_eq` is a definitional equality between
`OppositeSupport.jacquetAction` and the representation underlying
`CuspidalJacquetMultiplicity.oppositeJacquet`. Both use the actual opposite
unipotent coinvariants and inverse full upper modulus before transport to the
product Levi. This checks the compatibility needed to apply the published
opposite reciprocity construction to a maximal-cone quotient.

`gl_exists_surjective_from_oppositeInductionDual` applies that construction to a nonzero opposite-Jacquet map
of the input's smooth dual. It gives a nonzero map from the smooth dual into
actual normalized opposite induction. The first lemma then produces a
surjection from the smooth dual of this opposite induction onto the original
input. Smoothness of induction is intrinsic, so no smoothness or admissibility
premise on the inducing representation is needed for this adapter.

`gl_exists_surjective_from_reversedProductDual` treats a Jacquet map with target an actual block tensor.
The published `glOppositeProductReversal` equivalence transports the orbit map
to actual upper normalized induction of the reversed blocks. Injectivity of
the equivalence preserves nonvanishing. Applying the first lemma gives an
actual surjection from the smooth dual of this reversed upper product onto
the original input. The normalization comparison, including its positive
half-modulus and right-translation conventions, is supplied by that imported
reversal theorem.

The conclusion still involves a dual of induction. It supplies no
identification with a tempered standard module. The independent selection,
block temperedness, analytic dual preservation and product-duality obligations
remain open. No new literature claim is made.
