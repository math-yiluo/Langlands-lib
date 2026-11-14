# Detecting isomorphisms of supplied homomorphisms modulo nil ideals

`NilIdealHomIsomorphismStatement` concerns a given homomorphism `f : G ⟶ H`
of actual group schemes over `Spec R`. The ring is arbitrary and commutative,
the source group is smooth, and the target is locally of finite type. For
any ideal `I` contained in the nilradical of `R`, if the actual pullback of
`f` to `R / I` is an isomorphism, then `f` is an isomorphism. The theorem
`nilIdealHomIsomorphism` proves this full-universe statement using
`isIso_of_nilIdeal_baseChange`.

The result assumes neither locality nor affineness nor reductivity. It uses
no nilpotence exponent for `I` or the nilradical.

The proof is an internal consequence of the published fibrewise
isomorphism criterion and elementary quotient-ring properties.
`fieldPoint_factors_nilIdeal` factors every field-valued point through
`Spec(R / I)`: a homomorphism to a field has a prime kernel, which contains
the nilradical, so the quotient universal property supplies the factor.
Consequently, on every residue-field fibre, the supplied homomorphism is
an isomorphism. The proof uses the canonical successive-pullback comparison
to identify this fibre with a pullback of the given quotient isomorphism,
and applies
`SmoothIsomorphismLocus.isIso_of_group_residueField_fibres`.

This does not construct a homomorphism between two groups from an
isomorphism over the quotient. In particular, it does not prove
`ReductiveNilradicalIsomorphismReflectionStatement`. It shows that, for a
prospective lift of a quotient isomorphism, invertibility follows from the
stated geometric hypotheses; constructing that lift remains a separate
deformation problem.
