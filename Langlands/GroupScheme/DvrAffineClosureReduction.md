# The conditional affine-target reduction over a DVR

This is a derived consumer of the generic-subgroup closure and its flat-source
factorization. Raynaud's `DvrGenericAffinenessStatement` is an explicit premise;
this module supplies no proof of that criterion or of the reductive-monomorphism
theorem.

For a DVR `R : Type u` with a specified fraction field `K : Type u`, let `M`
be a flat affine group of finite type over `Spec R`, and let `G` be a separated
group of finite type over the same base. For a homomorphism `f : M ⟶ G` whose
underlying scheme morphism is monic, `affineClosure` constructs the actual
schematic closure of its generic image as an affine flat group of finite type.
The type `Data M G f` records that target, its closed inclusion into `G`, the
monic factor of `f`, and the exact factorization equation. It also records an
isomorphism from `M_K` to the generic fibre of the target, identifies that
isomorphism with the base change of the factor, and identifies the inclusion's
kernel ideal with the kernel of the original generic map to `G`. Thus the
closed target is the schematic closure, rather than a chosen larger subgroup.

`Data.isClosedImmersion_iff` says that the original map is closed if and only
if its factor is closed. `FlatAffineCase` is the remaining assertion for
monomorphisms from reductive groups over DVRs into flat affine finite-type
targets. The theorem `dvrCase_of_flatAffineCase` deduces the published full
`ReductiveMonomorphismValuativeReduction.DvrCase` from that assertion and
Raynaud's criterion. It chooses `FractionRing R` and obtains the source
flatness and finite type from smoothness and its affineness from reductivity.

## Proof and provenance

The generic base change is monic because pullback of relative schemes preserves
monomorphisms and the forgetful functor preserves them as well. The published
`finiteTypeMonomorphism` theorem then proves that
generic map is a closed immersion. Both generic groups are separated and of
finite type; affineness supplies source separatedness and quasi-compactness.

Apply `GenericSubgroupClosure.closureGroup` to this closed generic map. Its
inclusion is closed, its structural morphism is flat, and finite type and
separatedness are inherited from the ambient group. The flat-source
factorization uses the identity of `M_K` as its supplied generic map. Its
base change is therefore exactly `genericToClosureIso.hom`. Transport of
affineness along this isomorphism proves that the closure has affine generic
fibre. Applying the supplied Raynaud criterion to the closure and its
separatedness proves that the closure is affine.

Closedness of the factor implies closedness of its composite with the closed
inclusion. Conversely, if the composite is closed, the separated inclusion
allows the factor to be a closed immersion as well. These are the two
directions implemented in `Data.isClosedImmersion_iff`.

Conrad, *Reductive group schemes* (2014), proof of Theorem 5.3.5,
printed/PDF p.166, motivates exactly this step: after the DVR reduction, take
the schematic closure of the generic image in the possibly nonaffine target,
factor the flat source through it, and invoke Raynaud to obtain an affine flat
target. Registered source `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The data package and the general flat affine source scope are internal derived
interfaces. No source claim that Raynaud has already been proved in Lean is
made.

The criterion itself is the published statement corresponding to Prasad--Yu,
*On quasi-reductive group schemes*, Proposition 3.1, author-preprint p.5.
It is an explicit premise here; the Library proves it only conditionally, in
`DvrGenericAffinenessReduction`. Subsequent embedding into a general
linear group and the reductive-group arguments are not part of this module.
