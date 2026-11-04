# Smooth real descent from the local-point structural inputs

Author: Worker 20.

This derived construction isolates the elementary group and topology part of
the route to Renard V.3.19. The original local-point compactness,
cocompactness and derived-annihilation targets remain explicit parameters.
This module does not establish the unconditional
`RationalSmoothRealDescentStatement`.

The generic lemmas in `Langlands.SmoothRealDescent` work for an arbitrary
topological group and a torsion-free target group. An open kernel on a compact
group has finite coset space. The subgroup index is nonzero and every group
element raised to that index belongs to the kernel. Injectivity of the power
map in the target forces the original value to equal one. Restricting this
argument to a compact subgroup proves `compact_subgroup_le_ker`.

For subgroups `H ≤ U` with compact coset space `G / H` and `U` open, the
ordinary coset map `G / H → G / U` is continuous and surjective. Its target is
compact and discrete, hence finite. No normality is required. Applying this
to an open kernel containing `H` proves `eq_one_of_cocompact` by the same
index and power argument. No topology or continuity assumption on the target
group is needed.

The actual-point construction uses the existing actual objects. For every
nonarchimedean local field `F : Type u` and connected reductive group scheme
`M`, put `K = rationalCommonNormKernel M`, `Z = schemeCenterPoints M` and
`D = (derivedSubgroup M).carrier (Over.mk (𝟙 _))`. The three inputs are
`CentralNormKernelCompactness M hM`,
`CentralDerivedNormKernelCocompactness M hM` and
`DerivedSmoothRealAnnihilation M hM`, all imported from
`Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement`.
Affineness is derived from `hM.isAffineHom` and the exact topology is
`rationalPointTopology F M.X`. Smoothness from `hM.smooth` supplies local
finite type; `rationalPoint_isTopologicalGroup` from
`Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups` then gives
the needed group topology.

Given an open-kernel homomorphism `f : M(F) →* Multiplicative ℝ`, compactness
kills `Z ⊓ K`, and the derived-point input kills `D`. Their join, restricted
to `K`, is therefore contained in the kernel of `f` restricted to `K`.
Cocompactness and the open-kernel argument imply `K ≤ f.ker`. The proof
neither identifies algebraic derived points with abstract commutators nor
assumes finite index of a central isogeny's image on rational points.

`rationalSmoothRealDescendOfStructure` applies
`rationalImageRealDescend` from
`Langlands.Representation.Plancherel.RationalImageRealDescent` to this proved
kernel inclusion. It constructs a real additive functional on the actual
valuation image and has the exact evaluation formula
`phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd`.
The intrinsic uniqueness lemma uses surjectivity of that projection to
characterize this constructed functional. The final intrinsic lemma
`rationalSmoothRealDescent_of_structure` packages
the kernel conclusion and unique factorization as the conditional implication
`SmoothRealStructureStatement.{u} → RationalSmoothRealDescentStatement.{u}`.
It retains arbitrary universe and equal or mixed characteristic. All three
structural proofs are still needed to use it for the task's unchanged
unconditional endpoint.

The provenance is internal and derived from the published actual-object
interfaces and Mathlib's coset, compactness and torsion-free APIs. The
construction is a formal reduction within the assigned proof route, not a
new translation or a claimed proof of the source's structural assertions.
