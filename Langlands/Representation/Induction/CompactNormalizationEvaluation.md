# Evaluation of normalized compact-induction transport

`normalizedTransport_eval` evaluates the actual normalized transport on compact
functions. Equality of the inducing subgroups leaves the point argument
unchanged. The ambient character multiplies the integral value, and the
coefficient equivalence postcomposes that value. The proof eliminates subgroup
equality and commutes the scalar through the coefficient linear equivalence.

`normalizedTransportEvaluation` packages the actual value function with two
identities: equality with evaluation of normalized transport, and the explicit
character-times-integral formula. The first proof is reflexivity and the second
is the evaluation lemma. This internal derived construction lets specializations
retain both proofs without reconstructing their action indices. It assumes an
existing integral equivalence and coefficient equivalence; it proves no
geometric comparison or structural existence.
