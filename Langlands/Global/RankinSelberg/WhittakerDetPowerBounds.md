# Determinant power bounds for Whittaker functions and derivative words

These internal lemmas are derived from the published Whittaker averaging and
finite derivative-word expansion. They are preparatory estimates for the global
simple-root majorization problem; they assert no gauge construction or
convergence theorem.

`norm_whittaker_le_of_detPower` preserves a bound
`‖f(g)‖ ≤ B |det g|^β` under Whittaker averaging. The determinant norm of every
adelic upper unipotent is one. Therefore the same bound holds along the whole
left unipotent orbit of `g`, and the published `norm_whittaker_le` applies.
It uses the normalized probability measure of the unipotent rational quotient
and the unit norm of a standard additive character.

`exists_norm_whittaker_pow_le_of_detPower` assumes that every vector of a
`WhittakerDecayClass` has a bound with the same determinant exponent `β`.
For a fixed vector and word length `K`, choose bounds for the finitely many
fixed matrix-unit derivative words applied to that vector. Their sum is a
nonnegative constant `B`, independent of the derivative matrix `Z`, the point
`g`, and the standard additive character. The published
`norm_whittaker_pow_le` bounds the Whittaker function of `(R Z)^K f` by the
sum of those word Whittaker functions times `(coordConst F * A)^K`, when
every entry of `Z` has norm at most `A`. Apply the first lemma to each word
and factor the common determinant power out of the finite sum.

These are formal consequences of Library lemmas, rather than separately
numbered assertions of the analytic literature. Finite-place support,
simple-root frequency estimates and the construction of a Schwartz–Bruhat
majorant remain separate obligations.
