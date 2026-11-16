# Removing a supplied finite normal kernel subgroup

`Langlands.GroupScheme.reductiveKernelQuotientFactorization` removes a
supplied finite flat normal kernel subgroup from a specified fibrewise
isogeny. It works over any affine scheme `S`, in every universe. Its inputs
are reductive group schemes `G` and `H`, a homomorphism `f : G ⟶ H` that
is an isogeny on every residue-field fibre, and a subgroup homomorphism
`i : N ⟶ G`.

The underlying morphism of `i` in `Over S` must be monomorphic; the structure
morphism of `N` must be finite, flat and locally of finite presentation.
The full range subgroup functor of `i` must be normal, and `i ≫ f = 0`.
One also supplies a field `k`, a point `b : Spec k ⟶ S`, and equality of
the full range of the actual base change of `i` with the full kernel range
of the actual base change of `f` at `b`.

The result, `ReductiveKernelQuotientFactorization f i b`, contains an
actual `ReductiveFiniteNormalSubgroupQuotient i` and a specified remaining
homomorphism from its quotient to `H`. Its `fac` field identifies the
composite with the original `f`; `fibrewise` proves the remaining
homomorphism is an isogeny on every residue-field fibre; `isIso` proves
that the actual base change of this remaining homomorphism at `b` is an
isomorphism. The inherited quotient projection is finite, flat and
surjective, and its target is reductive. No abstract isomorphism of fibre
objects replaces the assertion about the specified remaining map.

This is an internal composition of
`reductiveFiniteNormalSubgroupQuotient`, `FppfHomDescent`,
`FppfQuotientComparison`, and the fieldwise transport results of
`Langlands.GroupScheme.Reductive.FibrewiseIsogenyBaseChange`.

The helper `KernelQuotientFactorization.kernel_comp_eq_zero` uses equality
of the quotient's full kernel range with the range of `i` to show that
`f` kills the actual kernel. `FppfHomDescent.hom` then constructs the
remaining homomorphism and proves the exact factorization.

To retain the fibrewise isogeny condition, the proof works at every actual
field-valued point of `S`. The base-changed quotient projection is flat
and surjective, and its composite with the base-changed remaining map is
the base change of `f`. In
`KernelQuotientFactorization.isIsogeny_of_comp`, flatness descends along
the first map. Universal closedness of the second map follows from
universal closedness of the composite and surjectivity of the first.
Its source is locally of finite type over the base, so the second map is
locally of finite type; the affine source and target make it affine and
separated. It is therefore proper and affine, hence finite. Surjectivity
follows directly from that of the composite. The reductivity of the
quotient supplies the needed affine and finite-type properties of the
field fibres.

At the chosen point `b`, both the quotient projection and `f` are fppf
quotients of the same full kernel. Local finite presentation of the
base-changed `f` follows from smoothness of the group structure maps and
`locallyOfFinitePresentation_of_comp`. Finiteness gives
quasi-compactness for both maps. The published comparison isomorphism
between the two quotients has composite equal to `f`.
`KernelQuotientFactorization.isIso_of_same_kernel` uses quotient
epimorphism cancellation to identify this isomorphism's forward map
with the actual remaining homomorphism.

The finite flat normal subgroup is an explicit input throughout. This
construction does not establish its existence over a Henselian DVR.
That existence and the remaining global reductions are still needed
for `ReductiveFibrewiseIsogenyStatement`.
