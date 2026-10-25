# Proof of polynomial rigidity under reciprocal reflection

Worker 351 proves `Langlands.RankinSelberg.reflectionRigidity` with exactly the
closed type `Langlands.RankinSelberg.ReflectionRigidityStatement`.

The proof first evaluates the supplied rational identity at an arbitrary nonzero
complex point. It uses the published `RationalEvaluation` lemmas to establish
regularity of the constant, the arbitrary integer power of `RatFunc.X`, and the
actual reflected polynomial before applying multiplication and substitution
under evaluation. This yields

\[
D(z)=c z^m E(\delta/z)\qquad(z\ne0).
\]

If `D(z) = 0`, its constant coefficient one excludes `z = 0`. The nonzero
multiplier `c z^m` forces `E(delta/z) = 0`. The two open-disk exclusions then
give `a ≤ norm z` and `b ≤ norm (delta/z)`. Since `z` is nonzero, the norm of
the quotient gives `b * norm z ≤ norm delta`; multiplication by the positive
`b` yields `a*b ≤ norm delta`, contradicting the strict gap. Thus `D` has no
complex roots. The private helper `normalized_eq_one_of_no_roots` uses
Mathlib's `Complex.exists_root` to show its degree is at most zero, and its
constant coefficient then makes `D = 1`.

For a putative root `w` of `E`, the same normalization excludes zero. Evaluate
the identity at the nonzero point `delta/w`. The field identity
`delta/(delta/w) = w`, the root equation and `D = 1` yield `1 = 0`.
The same helper therefore proves `E = 1`.

This is an internal algebraic proof of the published statement. It relies on
Mathlib's fundamental theorem of algebra and the Library's existing rational
evaluation and reciprocal substitution results. The motivating JPSS provenance
and consumer obligations are recorded in
[the statement rationale](ReflectionRigidityStatement.md); this proof makes no
additional claim about that literature. It retains arbitrary complex units,
arbitrary integer exponents, the explicit root exclusions, normalizations and
strict radius gap. It supplies no representation-theoretic or analytic input
for applications.
