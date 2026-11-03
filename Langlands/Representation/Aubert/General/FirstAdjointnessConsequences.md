# Nonvanishing consequences of actual normalized first adjointness

Worker 1216 derives these internal consequences of the actual normalized
first-adjointness equivalence. The hypotheses are the same actual semidirect
decomposition `P = M ⋉ U`, closedness of `U`, local compactness and
nonarchimedeanness of `G`, and explicit `IsUnimodularModulus U hU`.
The group universe and the two representation carrier universes remain
independent. No finite-length or admissibility premise is used.

`equiv_comp` and `equiv_inducedMap` express naturality in the smooth source and
inducing representation. The proofs compare the actual maps on quotient
generators. Both sides evaluate the same induced function at the identity.

`equiv_ne_zero` uses injectivity and linearity of the Hom-space equivalence:
only the zero map can have zero adjoint. Consequently
`nontrivial_jacquet_of_map_ne_zero` gives a nontrivial carrier for the actual
normalized Jacquet module whenever there is a nonzero map into normalized
induction. A subsingleton carrier would make its adjoint zero.
`nontrivial_jacquet_of_injective` applies this to every nontrivial smooth
subrepresentation of the actual induction.

When the inducing representation is irreducible, `equiv_surjective` makes
this nonzero adjoint surjective by the generic simple-module result.
`quotientMapOfNonzero` packages that same actual descended evaluation
intertwiner with its surjectivity proof. If the source Jacquet module is also
irreducible, `equivalenceOfIrreducibleJacquet` packages the adjoint as an actual
representation equivalence, allowing independent carrier universes. There
is no assertion of semisimplicity or splitting.

The declaration-level dependencies are
`General.FirstAdjointness.equiv`, its quotient-generator formula, and
`Jacquet.Localization.hom_ext`; the naturality proofs use the actual map
definitions of `General.jacquetFunctor` and
`General.normalizedInductionFunctor`. Surjectivity and bijectivity use
Mathlib's `Representation.IsIrreducible.surjective_or_eq_zero` and
`Representation.IsIrreducible.bijective_or_eq_zero`.
The first-adjointness equivalence itself is constructed from evaluation,
localization-at-one quotient descent, the actual normalization cancellation
and smooth orbit functions, as described in its paired Markdown.
No classification, character-independence, geometric-lemma or
cuspidal-support theorem is used in these consequences.

This unit proves nonvanishing for subobjects of induction. Nonvanishing for
quotient constituents, an actual two-factor geometric sequence, the vanishing
at other proper standard subsets and the full
`RationalRankOneJacquetModulesStatement` remain separate proof obligations.
