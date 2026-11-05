# Specialization of the actual normalized models

Worker 1585. Derived from the published tensor evaluation, actual full
smooth induction, character-one relation quotients, and constant
normalizing characters. Waldspurger 2003 I.5, printed p.245, and IV.1,
printed p.277 (`waldspurger-2003-plancherel`) motivate the construction.
No algebraic-family finiteness or specialization isomorphism is asserted.

`tensorEvaluation ν V χ` bundles exactly
`unramifiedTensorEvaluation ν V · χ` as a semilinear map along
`evaluation ν χ : B →+* ℂ`. Its scalar law evaluates every B coefficient,
and `tensorEvaluation_action` is the actual unramified-twist action law.

`complexInducingRepresentation` inflates `Langlands.twist χ σ` along the
actual projection and uses the positive half-character on the full P.
`ComplexInduced` is the existing full smooth function space for that
action, with right translation `complexInducedRepresentation`.
`ComplexJacquet` is its actual character-one relation quotient, and
`complexJacquetRepresentation` uses the inverse Levi half-character.

`inducingEvaluation_action` uses evaluation of the constant full-P
normalizer and the published tensor action formula. `inducedEvaluation`
then applies `fullInductionEvaluation`, a generic semilinear
postcomposition construction, at each value. Covariance follows from
the inducing action identity. The same open subgroup that fixes the entire
original function fixes the evaluated function, so its uniform smoothness
condition is preserved. The semilinear map laws follow valuewise, and
`inducedEvaluation_action` is the right-translation identity.

The generic helper `relations_le_comap` proves that every semilinear
equivariant map takes the relation span at character one into the target
relation span: each generator maps to the corresponding target
generator. `quotientEvaluation` applies `Submodule.mapQ` along that map.
`jacquetEvaluation` applies this construction to `inducedEvaluation`;
`jacquetEvaluation_mk` is the exact canonical-quotient compatibility.
The helper `quotientEvaluation_action` reduces equivariance to quotient
representatives. `quotientEvaluation_twist_action` combines that identity
with semilinearity and the evaluated normalizing scalar.
`jacquetEvaluation_action` specializes this helper to the actual constant
inverse-half normalizer. All three evaluations are semilinear along the
same actual scalar evaluation.

For any smooth original representation A,
`complexInducedRepresentation_eq_functor` identifies the induced action
with the existing functor by equality, and
`complexJacquetRepresentation_heq_functor` identifies the quotient action
by heterogeneous equality (with definitionally identical carriers).
The first proof is reflexivity. For the second proof, the smooth object
bundled from the explicit induced action equals the existing normalized
induction object by reflexivity. Applying the normalized Jacquet functor
to that equality and then dependent congruence for the representation
projection gives the heterogeneous action equality.
The corresponding functors are
`Aubert.General.normalizedInductionFunctor` on `A.twist χ`, and its
`normalizedJacquetFunctor`. The smooth character certificate is the
existing `unramifiedCharacter_isOpen_ker`; the norm index family remains
unrestricted. No full-P/inflated-Levi character comparison is used.
Coefficient-intertwiner naturality is supplied separately.
