# Stabilizer-compatible coordinates on actual Lie weight lines

This internal construction extends the published coefficient Galois transport
of actual dual-number Lie kernels and their intrinsic all-test action weight
spaces. It uses the internal Hilbert 90 line-descent construction. All fields,
groups and their coefficient algebras retain arbitrary universe `u`.

For commutative rings `k` and `L` and an actual affine group scheme `G/k`,
composition and identity of the coefficient maps prove the corresponding
laws for `Lie.baseChangeGaloisEquiv`. These maps therefore give an additive
Galois action on the Lie kernel of the actual base change `G_L`. The action
is semilinear with the ordinary coefficient action of `Aut_k(L)` on `L`.

Now let `k` and `L` be fields and let `a` be an actual action of a commutative
group scheme `T` on an affine group scheme `U`, all defined over `k`. If a
subgroup `H` of `Aut_k(L)` fixes a character `chi` of `T_L`, the canonical
Galois maps preserve its actual action weight space. Membership here is the
published intrinsic eigenvector condition after every coefficient-algebra
extension and at every acting point. Restriction gives an additive semilinear
action on that actual subspace, without a supplied action on it.

When `L/k` is finite and this weight space has dimension one, Hilbert 90
gives an `L`-linear equivalence from `L` to that space for which applying
`sigma` to the actual Lie vector agrees with applying `sigma` to its
coordinate. Finally the construction specializes to the actual stabilizer
of an actual root under the published ordinary character Galois action,
using the conjugation-action comparison. No Galois assumption on the finite
extension is needed. The noncomputable definition
`rootWeightEquivariantLinearEquiv` chooses this actual linear equivalence;
`rootWeightEquivariantLinearEquiv_galois` proves the same intertwining law
for that chosen map, for every stabilizer element and coefficient.

The dimension-one hypothesis is explicit and is not proved here. This unit
neither realizes an actual root subgroup nor transfers such a subgroup's
dimension to its intrinsic adjoint weight space. It does not prove that a
relative-root restriction fiber is one Galois orbit, identify rational root
groups with field coordinates, or construct R1 data, a globally compatible
valuation family or an apartment.
