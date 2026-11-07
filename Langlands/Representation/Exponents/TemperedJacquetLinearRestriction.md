# Linear restriction of actual Jacquet intertwiners

This derived supporting construction makes the restriction argument of the
published `TemperedJacquetRestriction` usable for cardinal rank bounds when
the source and target carriers have independent universes. In particular,
induction of an object with carrier universe `v` can have carrier universe
`max u v`, while the inducing object retains universe `v`.

The construction imports and reuses the actual Jacquet parts, the Levi-point
transport, the inclusion `leviUnitaryJacquetModuleι`, the generalized-weight
transport theorem and the vanishing of nonunitary weights in a tempered
target. It adds no representation-theoretic existence assertion and cites
no new external source. Its provenance is the algebraic argument described
below. The existing equivalence of morphism sets in
`leviUnitaryJacquetRestrictionEquiv` is not replaced or changed.

## Inputs and maps

The context is the existing represented rational parabolic over an arbitrary
nonarchimedean local field, with rational Levi, matching geometric radical,
semidirect-product scheme isomorphism and split component. The canonical
point topologies are retained. The locally compact nonarchimedean point
groups and affine hypotheses are explicit as in the imported restriction
module. The ambient representation has carrier in `Type v` and the Levi
target in `Type w`, independently of each other and the field universe `u`.

`leviJacquetIntertwiner_eq_zero_on_nonunitaryPart` extends the published
vanishing argument to actual `Representation.IntertwiningMap` between these
independent carriers. It requires normalized-exponent temperedness of the
target. No temperedness or admissibility of the source is needed. For each
nonunitary normalized split-component weight, the published
`map_mem_generalizedWeightSpace_of_comp` sends its vectors into the same
weight of the target. The published
`tempered_generalizedWeightSpace_eq_bot` makes that weight zero. The
submodule supremum defining the nonunitary Jacquet part is therefore
contained in the kernel of the given map. This is the same generalized-weight
argument as the imported homogeneous-universe vanishing lemma; no new
Jacquet comparison or exponent theorem is asserted.

`leviUnitaryJacquetRestrictionLinearMap` is precomposition with the actual
unitary-part inclusion, on algebraic intertwiner spaces. Pointwise addition
and complex scalar multiplication show that it is complex-linear. It has no
temperedness or spanning premise.

## Injectivity and rank

The injectivity theorem assumes the target is normalized-exponent tempered
and that the underlying unitary and nonunitary submodules span the whole
Jacquet carrier. This spanning equality is explicit; disjointness is not
needed. Decompose a vector as a sum of a unitary vector and a nonunitary
vector. Maps with the same restriction agree on the first and both vanish
on the second, so they agree on the original vector.

`leviJacquetHom_rank_le_one_of_unitaryPart` applies Mathlib's rank bound for
an injective linear map. Thus a supplied cardinal rank bound of at most one
for maps from the unitary part implies that bound for maps from the whole
Jacquet module. Both intertwiner spaces use the same combined carrier
universe even though their two arguments need not have equal universes;
no finite-dimensionality or resizing premise is introduced.

The unitary-part rank bound, the spanning equality and target temperedness
are still inputs. This module does not prove the weak Jacquet decomposition
of actual induced square-integrable representations, nor construct regular
twists, nor prove generic irreducibility. It supplies the linear restriction
step needed to use such a decomposition in the existing proof task.
