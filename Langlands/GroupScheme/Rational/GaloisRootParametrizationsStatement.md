# Compatible parametrizations of a Galois-stable family of roots

Provenance: internal. This is a focused prerequisite for the merged-root
construction in `EvenChainGaloisDataStatement`. It extends the scope of the
published compatible simple-root map construction to an arbitrary indexed
family of roots. It asserts an existence proposition and supplies no proof.

The fields `k` and `K` are arbitrary, in one arbitrary universe, with a finite
Galois extension `K/k`. The affine group scheme `G` is defined over `k`.
A supplied split pinning `p` of its base change includes connected reductivity,
a split maximal torus and an actual root datum. The torus is identified by
`eT` with the base change of a ground-field commutative group scheme `T`, and
the pinned inclusion agrees with the base change of `i : T.toGrp ⟶ G` under
this identification.

An arbitrary type `J` carries an action `ρ` of the Galois group, and
`α : J → p.rootIndex` assigns an actual root index to each member. The
hypothesis says that these roots transform under the ordinary Galois action
on the character lattice of the descended torus. Neither injectivity nor
finiteness of `J` is required. Repeated root indices are allowed.

The conclusion supplies, for every `c : J`, an actual root parametrization
of `α c` in the sense of `SplitPinning.RootParametrization` (defined in
`SteinbergModifiedRootProduct`):
it represents the whole intrinsic root subgroup, is a closed subgroup map,
and is torus equivariant. Its rational point at every `s : K` satisfies
`σ(x_c(s)) = x_(ρ σ c)(σ s)` for the canonical rational conjugation on the
base changed group. This is a rational-point compatibility conclusion;
no normalization to the simple-root pinning vectors is imposed.

The intended proof route is to choose stabilizer-fixed nonzero Lie vectors
by the published Hilbert 90 weight-line descent, extend them equivariantly
around each orbit, and normalize actual root maps to those vectors. One must
establish existence and uniqueness with the prescribed nonzero derivative
for these arbitrary roots and check the comparison with rational conjugation.
The existing compatible simple-root construction alone does not discharge
those arbitrary-root obligations.

For an even-path consumer, `J` can index the selected paths and `α c` can be
the merged root at the middle pair. A path may be reversed by Galois
transport: its merged root is still the sum of its two middle roots, so the
stated root-transport condition has the same form for either orientation.
Canonical opposite pairs can then supply compatible root-generated reflection
points. This proposition does not assert the adjacent-root commutator or
absorption laws, coroot-point transport, orbit ordering, or stability of the
full pattern set; those remain separate obligations. It adds no restriction
on characteristic, perfectness, infinitude or simple connectedness.
