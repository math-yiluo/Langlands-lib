# Conditional derived-point inclusion into an ambient smooth real kernel

Authors: Worker 1374 (implemented reduction) and Worker 1512 (proposed
factorization target and surrounding proof plan). This internal assembly
proves a conditional implication. The unrestricted target still requires
proofs of the two displayed premises.

`derivedSmoothRealAnnihilation_of_structure` takes precisely the two
propositions `PositivePowerTorusAdditiveFactorizationStatement` and `RelativeRootReflectionExistenceStatement`, both at arbitrary universe `u`.
Its conclusion is the unchanged published
`DerivedSmoothRealAnnihilationStatement.{u}`. The field has either
characteristic and carries the existing nonarchimedean local-field class.
The ambient kernel uses the canonical rational-point topology.

The factorization proposition is imported from the published
`Langlands.GroupScheme.Rational.PositivePowerFactorizationStatement`; it is
a proposition definition, and this reduction explicitly assumes its proof.
The reflection proposition is also retained as an explicit premise. All
other ingredients below are imported theorems. This pair supplies an
internal composition of those interfaces and makes no additional claim
about the original literature.

The implemented proof chooses the actual closed affine locally finite type
representative `d : D → G` of the algebraic derived subgroup using the
published representability theorem. The published derived-smoothness theorem
makes `D` smooth. The representing range equality lifts any actual derived
rational point to an actual point `y` of `D`.

Apply the positive-power factorization premise inside `D`: for some `m > 0`,
`y^m` is a product of an actual closed-torus point and the image of additive
coordinate `1` under an actual morphism from the standard vector group of
dimension one. Composing both morphisms with `d` puts their full images inside
the actual algebraic derived subgroup. Closedness of the torus immersion
into the affine locally finite type `D` supplies its affineness and local
finite type instances.

The conditional torus theorem kills the torus point using the reflection
premise and the published theorem
`Langlands.Plancherel.torusNormKernelCompactness`, imported from
`Langlands.Representation.Plancherel.TorusNormKernelCompactnessProof`.
This theorem supplies compactness of the actual rational-character norm
kernel in the canonical topology for every local-field torus of either
characteristic; compactness is no longer an input to this reduction.
`vectorImage_eq_one` kills the additive point without any
factorization premise of its own. Multiplicativity then gives `f(x)^m = 1`.
Torsion freeness of the additive real group forces `f(x) = 1`, proving the
required inclusion in the ambient kernel.

This route does not require reductivity or semisimplicity of the representative
`D`, equality of its rational points with abstract commutators, rational
surjectivity of a central isogeny, perfectness of the field, or rational Jordan
decomposition. It does require proofs of both remaining structural
propositions. Neither is supplied by this conditional reduction.

`derivedPointsToOpenRealKernel` is the resulting group homomorphism from
the actual algebraic derived-point subgroup to `f.ker`, under the same two
structural premises. It uses `Subgroup.inclusion` and the preceding conditional
annihilation theorem. Its coercion to the ambient rational-point group is the
original point, as recorded by `derivedPointsToOpenRealKernel_coe`. The
construction carries an affine-hom instance on `G` to form the canonical
topology; `IsConnectedReductive G` already supplies that property.
