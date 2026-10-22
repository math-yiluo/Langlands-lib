# The actual corner module on fixed vectors

For a smooth complex representation and a compact open subgroup K,
`cornerAction` is a unital complex algebra homomorphism from the actual
`HeckeAlgebra.Corner μ K hK` to the complex endomorphisms of the existing
`Langlands.fixedVectors ρ K.toSubgroup`. `cornerModule` supplies the resulting
unital module structure on precisely that submodule.

The group is an arbitrary-universe topological group with its Borel measurable
structure and a supplied Haar measure. The representation carrier is in an
independent universe and has only an additive commutative group and complex
module structure, with no topology or finite-dimensionality assumed. An actual
compact open subgroup is supplied. These hypotheses apply in the intended
Hausdorff locally compact totally disconnected setting.

The operator is the restriction of the previously constructed finite-fiber
integral `∫ g, f(g) • ρ(g)v dμ(g)`, using the positive `ρ(g)` convention and
the supplied left Haar measure. The unit is `e_K = μ(K)⁻¹ 1_K`, with the
positive finite Haar mass interpreted as a complex scalar. The corner embedding preserves the actual test
function and convolution. Its left invariance puts every output into the fixed
subspace. This gives `cornerActionLinear`, whose bilinearity is inherited from
the actual integrated action. The corner unit is the normalized indicator;
its previously proved action on fixed vectors is the identity. The proved
convolution law gives multiplicativity. These intrinsic laws construct the
unital algebra homomorphism and module; they are not input fields.

`cornerModule_isScalarTower` records compatibility with the already existing
complex scalar multiplication. `cornerAction_intertwiner` uses the published
`fixedVectorsMap` and naturality of integration. `cornerAction_equiv` applies
this law to the intertwiner underlying a representation equivalence and reuses
`fixedVectorsEquiv`. For L contained in K, `cornerAction_refinement` states
compatibility between the actual corner inclusion and the ordinary inclusion
of K-fixed vectors into L-fixed vectors. Both sides have the same underlying
vector by their definitions.

Finally `cornerAction_project` says that the corner projection of an ambient
Hecke function acts on a K-fixed vector by the ambient action followed by the
K-fixed projection. Its proof applies convolution multiplicativity to
`e_K * f * e_K` and uses that the rightmost normalized indicator fixes the input.

The provenance is internal construction of the natural Hecke module and
`e_K V = V^K` described in Flath, *Decomposition of representations into tensor
products* (1979), section 1, printed page 179, registered as
`flath-1979-tensor-products`. The finite-fiber implementation and restrictions
are project-derived proofs.

The imports `ActionProjection` and `Corner` are published Library modules.
They supply the actual integrated action, normalized-indicator projection and
compact-open corner algebra used by this construction.
