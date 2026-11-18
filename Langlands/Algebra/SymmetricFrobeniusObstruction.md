# The Frobenius symmetric-power obstruction

Over a field `k` of characteristic `p`, with `0 < p`, let `f` be a nonzero
nilpotent endomorphism of any `k`-vector space `M`. The theorem
`not_isProj_frobeniusSubspace_of_isNilpotent` proves that no projection from
the actual degree-`p` homogeneous component of `SymmetricAlgebra k M` onto
the span of its `p`th powers of linear generators commutes with the
endomorphism `homogeneous f p`. No finite-dimensionality, perfectness or
algebraic-closure assumption is needed for this algebraic assertion.

`frobeniusSpan` is the linear span of the elements `(ι x)^p` in the genuine
symmetric algebra. These elements belong to its existing degree-`p`
`homogeneousSpan`; `frobeniusSubspace` is that span viewed as a submodule
of the homogeneous component. `derivation_pow_eq_zero` uses the Leibniz
power rule and the vanishing of `p` in `k`. Linear-span induction proves
that the whole Frobenius span is killed by every `k`-derivation.

The proof first handles a chain `f x = y`, `f y = 0`, `y ≠ 0`. The induced
derivation sends `z = (ι y)^(p-1) * ι x` to `w = (ι y)^p`. Both elements
belong to the degree-`p` component. A projection `P` onto the Frobenius
subspace fixes `w`, while the derivative of `P z` is zero. Commutation
would give `0 = w`. A separating linear functional proves `ι y ≠ 0`;
the symmetric algebra of a vector space over a field is a domain, so
`w ≠ 0`. This is the contradiction implemented in
`not_isProj_frobeniusSubspace_of_chain`.

For the final specialization, a nonzero nilpotent endomorphism has
nilpotency class at least two. Evaluating its last nonzero power at a
suitable vector supplies the required chain. This is implemented in
`exists_chain_of_isNilpotent` using the least vanishing power.

This is the algebraic step of the source's proof of Nagata's theorem.
The source obtains `f` from a faithful representation of alpha_p and the
projection from a splittable representation of an ambient group. Those
representation-theoretic and group-scheme steps remain separate obligations;
this helper does not assert inheritance of linear reductivity by closed
subgroups or prove the full Nagata statement.

Source: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, Theorem 3.6, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
