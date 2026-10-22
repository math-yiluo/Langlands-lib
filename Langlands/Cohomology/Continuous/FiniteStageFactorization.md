# Finite-stage continuous factorization

This module constructs an ordinary finite-stage cochain isomorphism and supplies
internal construction certificates for the existing finite-stage
maps in `Langlands.Continuous.FiniteQuotientComparison`. It changes neither the
cohomology objects nor their maps. All groups, coefficients, and scalars live in an
arbitrary common universe `u`.

Let `k` be a commutative topological ring, let `G` and `H` be topological groups,
and suppose `H` has discrete topology. Let `A` be a discrete `G`-module, `N` an
open normal subgroup of `G`, and `B` a continuous `H`-representation. Fix a
continuous group homomorphism `φ : G → H` and an equivariant continuous linear
coefficient map `f : Res(φ)(B) → A`.

`finiteStageCochainMap_eq_of_factorization` starts with a cochain map `c` from the
ordinary finite-quotient stage to ordinary cochains of `B`. If composing `c` with
the ordinary map induced by `(φ,f)` gives the actual `ordinaryInflationCochains`,
then the actual continuous finite-stage cochain map equals `c`, followed by the
inverse discrete continuous-to-ordinary comparison, followed by the continuous
cochain map induced by `(φ,f)`, with topology forgotten. The proof cancels the
injective continuous-to-ordinary comparison on cochains and uses its naturality
and invertibility for the discrete group `H`.

`finiteStageToContinuous_eq_of_factorization` passes that equality to cohomology
in each natural degree `q`. It uses naturality of the forgetful functor's
`mapHomologyIso` to identify the result with the existing continuous cohomology
map. It requires no injectivity of the comparison on the cohomology of `G`.

`finiteStageCochainIso` constructs the ordinary cochain isomorphism from a group
equivalence `e : G/N ≃ H`, a linear equivalence `e' : A^N ≃ B`, and its
equivariance proof. Its forward map uses `e.symm` and `e'`; its inverse uses `e`
and `e'.symm`. Both inverse identities follow from ordinary cochain functoriality,
the inverse identities for the two equivalences, and `cochainsMap_congr`.
`finiteStageCochainIso_homologyMap` identifies its forward homology map with the
existing forward map of `groupCohomology.mapIso`, definitionally. The cochain
construction itself does not use discreteness of `H`.

`finiteStageToContinuous_eq_mapIso` gives a directly usable certificate. Its data
are a group equivalence `e : G/N ≃ H`, a linear equivalence `e' : A^N ≃ B`, and
its genuine equivariance proof. It requires the pointwise group formula
`e([g]) = φ(g)` and the coefficient formula `f(e'(x)) = x.val`. From these it
proves that `finiteStageToContinuous` equals the forward map of
`groupCohomology.mapIso e e'`, followed by inverse discrete comparison and the
actual continuous map induced by `(φ,f)`. The proof derives the ordinary
cochain factorization using `cochainsMap_comp` and `cochainsMap_congr`: the group
formula identifies `e.symm ∘ φ` with the quotient projection, and the coefficient
formula identifies the composite with the invariant-submodule inclusion. It
then applies the preceding all-degree certificate.

These results are internal consequences of the published project comparison
constructions and Mathlib's group-cohomology and homology functoriality. They are
not translations of a separate literature theorem. The discrete topology on `H`
is explicit; finiteness is not required for this general certificate. The
fixed-field application must separately construct the equivalences and prove
both pointwise formulas. This module alone asserts no fixed-field specialization,
vanishing, or H2 exactness result.

Author: Worker 54.
