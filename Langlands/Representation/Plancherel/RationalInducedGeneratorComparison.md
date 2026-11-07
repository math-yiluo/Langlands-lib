# Actual norm-kernel generator and universal normalized induction

This derived comparison uses the published compact-induction/tensor comparison
for the entire restriction to the common kernel of every rational-character
norm. It retains arbitrary independent field and original-carrier universes.
The rational Levi is affine and locally of finite type. The supplied parabolic
root presentation identifies its canonical point topology with the inherited
topology on the literal ambient Levi subgroup.

`literalLeviRep` pulls the original smooth representation back along this
canonical point homeomorphism. `rationalUniversalTensorLeviEquiv` tensors the
published equivalence of the full evaluation-generated regular algebras with
the identity on the original carrier. Tensor induction proves equivariance:
the algebra equivalence carries the regular evaluation factor at a rational
Levi point to the evaluation factor at its actual embedded point.

`rationalNormKernelUniversalLeviEquiv` composes the pullback of the published
compact-induction comparison with that tensor equivalence. It compares actual
compactly supported covariant functions with the native universal tensor,
viewed over the complex numbers by scalar restriction.

The semidirect decomposition and the closed unipotent subgroup determine the
same actual Levi projection and positive half modulus on both full parabolic
actions. `rationalNormKernelInducingEquiv` reuses the coefficient equivalence
after inflation and normalization. Complex linearity changes multiplication by
the complex half modulus into its image in the regular algebra.

`rationalNormKernelInducedEquiv` applies the function-level
`Induction.coefficientSmoothInducedEquiv`. Its source is exactly the published
`rationalInertiaInductionFunctor` applied to the actual norm-kernel compact
induction. Its target is the native full universal induced action with scalars
restricted to the complex numbers. The map postcomposes every function value
with the inducing equivalence, and preserves covariance and a uniform right
stabilizer; it does not replace either induced carrier with an abstract model.

This construction requires local compactness and the nonarchimedean group
structure on the ambient rational points for the normalization. It assumes no
irreducibility, admissibility, finite dimensionality, small-progenerator
property or coefficient-Jacquet finiteness. It supplies a representation
comparison, not the uniform stabilization theorem.

A private generic helper proves the inflation-and-constant-twist step before its application to the actual rational data. This keeps scalar compatibility on an arbitrary complex algebra explicit and avoids repeated elaboration of the large scheme-point expressions.

The included comparison statement and proof dependencies only replace unnamed local topology instances with explicit module-specific names, with matching documentation. Their previous generated names collided with the actual small-progenerator statement under combined imports; no topology, predicate, theorem statement or mathematical proof is changed.
