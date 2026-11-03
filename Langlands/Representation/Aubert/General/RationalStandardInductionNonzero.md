# Actual standard induction is nonzero on nonzero smooth objects

Author: Worker 1277.

`Langlands.Aubert.General.RationalPointFamily.rationalStandardInductionNonzero`
proves the whole exact internal
`RationalStandardInductionNonzeroStatement.{u,v}` with no additional theorem
parameters. The imported statement pair is preserved.

The proof chooses a standard cocharacter supplied by the target's existing
`StandardCocharacterStatement`. Its three subgroup identities identify the
exact standard parabolic, Levi and unipotent point subgroups with the actual
dynamic subgroups. After transport, proof irrelevance identifies the
semidirect-decomposition projection with the dynamic one.
`continuous_dynamic_projection` gives its continuity for the canonical
point topology. That published result constructs the continuous map through
the affine dynamic subgroup schemes and their rational-point homeomorphisms.

For a smooth representation of the Levi, `isSmooth_comp` makes its inflation
smooth. `isSmooth_twist_iff` and the open kernel of the intrinsic half Haar
modulus make the normalized inducing action smooth.
`Induction.compactLocalSection` then constructs a compactly induced function
with any prescribed value at the identity, by taking the quotient
neighborhood to be the whole space. `compactLocalSection_apply` proves that
value. Its underlying smooth function proves surjectivity of evaluation.
A surjection onto the nontrivial inducing carrier gives nontriviality of
the normalized induced carrier.

This internal derivation uses actual standard rational points and the
actual normalized functor. It adds no parabolic-closedness or
projection-continuity premise to the whole proposition. It uses neither
classification, character independence, geometric lemma, adjointness nor
cuspidal support, and it proves no length bound or two-constituent result.
