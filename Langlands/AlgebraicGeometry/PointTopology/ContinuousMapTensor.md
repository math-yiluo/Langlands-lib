# Finite projective extension of continuous functions

Worker 105 constructs a derived algebraic tool for the point-topology comparison
in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 2.4, printed page 3, registered source
`conrad-2011-weil-grothendieck-adelic-points`. This continuous-function
formulation is a derived proof tool, not an assertion transcribed from Conrad.

For an arbitrary commutative topological ring `A`, a finite projective
commutative `A`-algebra `B` equipped with its module topology, and any topological
space `X`, `continuousMapTensorAlgEquiv` is the actual `B`-algebra equivalence
`B ⊗[A] C(X,A) ≃ₐ[B] C(X,B)`. The forward homomorphism sends `b ⊗ f` to
`x ↦ b * algebraMap A B (f x)`. It is obtained from the tensor-product
adjunction and continuous postcomposition by the scalar map. The topology on
`B` makes it a topological ring by Mathlib's finite-module theorem. The API
takes this topological-ring instance explicitly; it can be supplied by
`IsModuleTopology.isTopologicalRing A B`. It is therefore no additional
restriction on the finite algebra with its module topology.

The bijectivity proof chooses a split finite-free presentation of the
finite projective module `B`. Its finite coordinate functionals are continuous.
They give a preimage for any continuous `B`-valued function by a finite tensor
sum. Tensor induction proves coordinate compatibility and reconstruction,
which imply injectivity. No topology on the continuous-function ring itself,
compactness of `X`, Hausdorffness, freeness, field or local-ring assumption
is used.

The finite projectivity hypotheses appear only in the bijectivity theorem and
the resulting equivalence. The forward homomorphism requires only the module
topology, which makes the scalar map continuous. The theorem
`eval_comp_continuousMapTensorAlgEquiv` identifies evaluation at each `x : X`
with the tensor extension of scalar-valued evaluation followed by
`B ⊗[A] A ≃ₐ[B] B`. Its proof is tensor induction, using the pure-tensor
formula and additivity. These identities fix the actual forward map and its
compatibility with all point evaluations.

This tool alone does not identify any Weil-restriction point spaces or prove
the source's homeomorphism. Those remain separate obligations.
