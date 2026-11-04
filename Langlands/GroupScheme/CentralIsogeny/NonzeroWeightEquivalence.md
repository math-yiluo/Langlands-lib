# Nonzero weight equivalences for central isogenies

Authors: Worker 1375 and Worker 1283.

This internal module constructs
`Lie.nonzeroWeightSpaceEquivOfCentralIsogeny`. For any central isogeny
`q : G ⟶ H` of affine locally finite-type group schemes over an arbitrary
field, any split torus acting through a homomorphism `i : T ⟶ G`, and
any nonzero character `χ`, the actual differential restricts to a linear
equivalence from `weightSpace i χ` to `weightSpace (i ≫ q) χ`.
The equivalence sends a source vector to its actual differential.

The surjectivity argument first treats a standard split torus. Let `m`
be the nonzero exponent vector of `χ` and work over its group algebra
`A = k[ℤ^I]`. Extend a target weight vector `X` to `A` and act by the
universal torus point. Worker 1283's actual commutator tangent lift,
`CommutatorDescent.range_adjoint_sub_id_le_of_centralIsogeny`,
provides a source Lie vector whose differential is the adjoint difference
`Ad(q(n))(X_A) - X_A`.

Take the coefficient of exponent `m`. The coefficient of the adjoint
term is `X`, by the published singleton coefficient formula for a weight
vector. The coefficient of the constant term is zero because `m ≠ 0`,
by `Lie.kernelCoefficient_monomial`. The proved
`Lie.kernelCoefficient_targetMapLinear` commutes this coefficient
extraction with the differential. Thus `X` already lies in the
base-field differential image; there is no need to extend the field or
divide by a scalar that might vanish in its characteristic.

Choose a splitting isomorphism to transport this range result to any
split torus. The proved `Lie.exists_weightSpace_preimage` then projects
an arbitrary differential preimage onto its specified character weight,
proving surjectivity on that weight space. The published central-kernel
injectivity theorem supplies injectivity: a differential kernel vector
has zero adjoint weight, and distinct split-torus weights are disjoint.
`LinearEquiv.ofBijective` constructs the asserted equivalence.

Finally, `roots_comp_eq_of_centralIsogeny` proves equality of root
supports for the same source torus. The equivalence reflects and
preserves whether every nonzero weight space is nontrivial.

All statements retain the full scheme-theoretic central kernel and
allow inseparable or nonsmooth isogenies, arbitrary fields and arbitrary
universe. Neither group is assumed smooth, connected or reductive, and
`i` need not be a closed immersion or maximal torus. The provenance is
internal, combining the actual descended commutator, actual Lie
coefficient maps, split-torus weight decomposition, and central-kernel
injectivity. This supporting unit does not prove the final
central-isogeny root-datum isomorphism criterion.
