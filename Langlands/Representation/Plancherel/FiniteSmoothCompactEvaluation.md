# Finite scalar-smooth families detected by compact evaluation

Worker 200. This is an internal linear-algebra and compactness construction for
Waldspurger VI.1's fixed compact model. It is derived from the existing
`finiteSmoothFamilies` definition and the finiteness of the quotient of a compact
group by an open subgroup. It adds no representation-theoretic hypothesis.

The parameter is a finite torus `J → Circle`. The complex coefficient spaces
`V` and `W` can have arbitrary dimension and independent universes; neither has
a supplied topology or norm. `mem_finiteSmoothFamilies_pi` proves that a finite
tuple is a finite scalar-smooth family whenever each coordinate is. Its proof
sums the coordinate inclusions of the given expansions.

`mem_finiteSmoothFamilies_of_injective_linearMap` reflects the same condition
along any injective complex-linear map. A vector-space linear left inverse
exists, and applying it to the finite expansion recovers the original family.

`rightInvariantEvaluationSubmodule E L` constructs the actual complex subspace
of `W` whose evaluations are right invariant under a subgroup `L`. This
construction requires only a group, the linear evaluation map and the subgroup.

The main theorem `mem_finiteSmoothFamilies_of_common_open_stabilizer` takes a
compact topological group `H`, an injective linear evaluation map
`E : W →ₗ[ℂ] (H → V)`, a family `F`, and a single open subgroup `L` such that
`E(F(z))(k*l) = E(F(z))(k)` for every parameter and every `l ∈ L`. If every
point evaluation is a finite scalar-smooth `V`-valued family, then the entire
`W`-valued family is finite scalar-smooth.

The proof uses the constructed subspace whose evaluations have that right stabilizer.
Evaluation on representatives of `H/L` is injective on this subspace: every
point differs from its representative by right multiplication by an element
of `L`. Compactness and openness make `H/L` finite. The finite-tuple theorem,
injection-reflection theorem and subspace inclusion finish the proof. Only
finitely many point-evaluation expansions are used.

This does not infer finite scalar smoothness from pointwise smoothness alone.
The common stabilizer and compactness supply the finite determining set. Its
intended consumer is the full product-group translation of actual coherent
orbit sections, where the common stabilizer and the evaluation formulas must
be proved separately. This module proves no orbit translation stability,
wave-packet estimate, inversion or Plancherel theorem.
