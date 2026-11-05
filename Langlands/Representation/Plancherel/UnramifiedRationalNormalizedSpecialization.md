# Actual rational-point specialization to the existing complex functors

Worker 16, using the generic specialization construction by Worker 1585; the
law formulation described at the end was revised by Worker 1585.
This derived application specializes the full rational-norm-family models of
`UnramifiedRationalNormalizedModels`. Its source motivation is Waldspurger 2003
I.5, printed p.245, and IV.1, printed p.277
(`waldspurger-2003-plancherel`). The stronger fiber-isomorphism assertions in
IV.1 and finiteness assumptions in I.5 are not part of this construction.

`evaluation r χ` evaluates the existing concrete regular algebra at the actual
unramified character χ. `tensorEvaluation r E χ` is exactly the published
`unramifiedTensorEvaluation` at χ, bundled semilinearly along this scalar map.
Its pure-tensor formula is b ⊗ v ↦ b(χ) v, with the original independent
coefficient universe. The full family `parabolicLeviRationalNormCharacters r`
is retained throughout.

`complexInduced` is directly the existing
`Aubert.General.normalizedInductionFunctor` applied to the actual smooth twist
of π by χ. `complexJacquet` is directly its image under the existing
`Aubert.General.normalizedJacquetFunctor`. The positive full-parabolic
half-character and inverse Levi half-character therefore have exactly the
existing functors' signs. Neither target is a selected isomorphic substitute.

`inducedEvaluation` evaluates each actual tensor-valued induced function at χ.
The imported generic construction proves covariance by tensor equivariance
and evaluation of the constant normalizing character; the original uniform
open right stabilizer also fixes the evaluated function. `inducedEvaluation_eval`
gives the actual pointwise formula, `inducedEvaluation_regular_smul` gives
semilinearity b ↦ b(χ), and `inducedEvaluation_action` gives equivariance for
right translation. `tensorEvaluation_inducing_action` identifies the tensor
specialization with the exact positively normalized complex inducing action.

`jacquetEvaluation` applies the generic `quotientEvaluation` helper directly
to the actual induced representation and the existing complex induced target.
It descends through the actual character-one unipotent-relation quotient:
the helper sends each relation to a relation and uses the quotient map's
universal property.
`jacquetEvaluation_mk` states the resulting commutative square for the actual
canonical quotient maps. `jacquetEvaluation_regular_smul` states the same scalar
evaluation law, and `jacquetEvaluation_action` proves equivariance for the
inverse-half normalized Levi actions.

`inducedMap` and `jacquetMap` are the B-linear maps induced by scalar extension
of an actual complex coefficient intertwiner. `complexInducedMap` and
`complexJacquetMap` apply the existing normalized complex functors to the
twisted coefficient map. `inducedEvaluation_map` proves naturality by function
extensionality and the tensor evaluation naturality law. `jacquetEvaluation_map`
applies `quotientEvaluation_natural`, whose proof reduces to actual quotient
representatives and that induced naturality law.
The component identity and composition laws are those of the imported generic
maps and the existing complex functors.

Each law above is stated through a reducible `Prop` abbreviation named like
the law in UpperCamelCase: `TensorEvaluationTmul`, `InducedEvaluationAction`,
`TensorEvaluationInducingAction`, `InducedEvaluationEval`,
`InducedEvaluationRegularSmul`, `JacquetEvaluationMk`,
`JacquetEvaluationRegularSmul`, `JacquetEvaluationAction`,
`InducedEvaluationMap` and `JacquetEvaluationMap`. Each abbreviation unfolds
to exactly the displayed equation, and the snake_case theorem proves it with
the same arguments, so the statements and their meaning are unchanged. A law
applied to its arguments elaborates against the displayed equation, including
its `.symm`, and `simp only [tensorEvaluation_tmul]` fires. In this concrete
setting `rw [inducedEvaluation_action]` and `simp only [jacquetEvaluation_mk]`
exceed the default heartbeat limit, exactly as they did for the unabbreviated
statements.

The only reason for this device is build performance. When a module is written
out, Lean 4.34 indexes the constants of every theorem signature for library
suggestions. On the fully elaborated equations of this concrete rational-point
setting, that indexing runs for minutes per theorem, so a single Lake build
exceeded an hour. With short theorem types the module builds in about half a
minute.

The actual affine rational-point and supplied semidirect/closed-unipotent inputs
are those of `ConditionalParabolicIntertwiningStatement`; no splitness,
characteristic, or finite-dimensionality restrictions are added. These maps
supply specialization, with no claim of surjectivity, fiber isomorphism,
commutation of scalar extension with induction, geometric filtration,
projectivity, rationality, or continuation.
