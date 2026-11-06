# Free tensor stability of cohomological triviality

`Langlands.Tate.freeTensorCohomologicalTriviality`, in module
`Langlands.Cohomology.Tate.FreeTensorCohomologicalTrivialityProof`, proves
`Langlands.Tate.FreeTensorCohomologicalTriviality.{u}`. For a finite group
`G` and integral representations `A` and `B` in the same arbitrary
universe, freeness of the underlying integral module of `B` and
cohomological triviality of `A` imply cohomological triviality of the
diagonal tensor representation `A ⊗ B`. The conclusion concerns actual
Tate cohomology in every integer degree on every subgroup. No rank bound
or condition on the action of `B` is required.

The implementation uses `IntegralScalar`, the existing universe lift of
the integers. The helper `integralModule_eq` proves uniqueness of its
module structure on an additive commutative group: every scalar is the
cast of its underlying integer, and integer scalar multiplication in any
module equals the additive group's canonical integer multiplication.
In the statement module, instance search elaborates the freeness premise
for the module structure `ULift.module` lifts from the canonical integer
module structure on the carrier of `B`. The proof module disables that
instance. It uses `integralModule_eq` to transport the premise to the
module structure carried by the representation. Freeness then supplies
flatness.

## Exactness and restriction

`flat_tensorRight_shortExact` proves that tensoring representations by a
flat underlying module preserves short exact sequences. The proof
forgets the group action, applies exactness of the module tensor
functor, and reflects the resulting short exact sequence through the
faithful forgetful functor. The symmetry of the module tensor product
transfers finite-colimit preservation from left tensoring to right
tensoring.

`restrict_cohomologicallyTrivial` proves that cohomological triviality is
preserved by restriction to a subgroup `H`. For a subgroup `J` of `H`,
the proof uses its image in `G` and the canonical isomorphism from `J`
to that image. The identity coefficient map intertwines the restricted
actions. The existing `reindexIso` transports the actual Tate complex
and its cohomology, so vanishing on the image gives vanishing on `J`.

## Finite p-groups

For a finite p-group `P`, the proof proceeds through three coefficient
cases.

1. `killed_tensor_isZero` treats a coefficient `A` killed by the prime
   `p`, with zero ordinary first cohomology. The existing
   `PGroupVanishing.exists_retraction` supplies an additive retraction
   onto the invariants. Its integral-linear form gives the existing map
   `toCoinduced`. The fixed-vector injectivity argument and the
   first-cohomology surjectivity argument make this map an isomorphism.
   The existing `coinducedTensor_tate_isZero` then gives vanishing of
   `A ⊗ B` for every `B`, without a flatness premise in this case.

2. `torsionFree_tensor_isZero` treats an acyclic `A` on which
   multiplication by `p` is injective, and a flat `B`. The cokernel `Q`
   of multiplication by `p` is killed by `p`. The Tate long exact
   sequence makes `Q` acyclic, so its ordinary first cohomology is zero.
   The first case makes `Q ⊗ B` acyclic. Flat tensor exactness and the
   long exact sequence then make multiplication by `p` injective on
   every Tate cohomology module of `A ⊗ B`. The order of `P` is a power
   of `p`, and the existing `PGroupVanishing.card_smul_eq_zero` shows
   that it annihilates Tate cohomology. Repeated injectivity of
   multiplication by `p` therefore forces every class to be zero.

3. `exists_coinduced_cover` constructs an epimorphism from a coinduced
   coefficient `coinduced T` onto any `A`, retaining that coinduced
   presentation. The underlying coefficient of `T` is the free module
   on the elements of `A`, with trivial action. Its evaluation map,
   followed by the existing coinduced projection, is surjective: a
   delta function at a basis vector maps to the corresponding element
   of `A`. Multiplication by `p` is injective on the covering
   coefficient. In `pGroup_tensor_isZero`, its kernel `K` is consequently
   also p-torsion-free. If `A` is acyclic, the Tate long exact sequence
   makes `K` acyclic. The second case gives vanishing of `K ⊗ B`, while
   `coinducedTensor_tate_isZero` gives vanishing of the covering tensor.
   Flat tensor exactness and the long exact sequence give vanishing of
   `A ⊗ B`.

These arguments use the existing actual Tate complexes, their
comparison with ordinary cohomology in degree one, the annihilation by
the group order, coinduced representations, and long exact sequences.
The explicit covering construction follows the published
`PGroupVanishing` covering argument while retaining the coinduced
witness needed for the tensor step.

## Arbitrary finite groups and the target

`tensor_isZero` applies the existing Sylow detection theorem
`sylowTateVanishing` to `A ⊗ B`. On each Sylow subgroup, cohomological
triviality of `A` supplies all-degree vanishing, and
`pGroup_tensor_isZero` applies with the same flat underlying module `B`.
The restriction of `A ⊗ B` is definitionally the tensor product of the
restrictions, so no comparison isomorphism is needed.

The final theorem first obtains flatness from the supplied freeness of
`B`. For each subgroup `H` of `G`, it applies `tensor_isZero` to the
restricted representations, using `restrict_cohomologicallyTrivial` for
the first factor. This supplies every subgroup and integer degree in
the exact target proposition.

This proof is an internal implementation of the statement's documented
free-factor consequence of Serre's tensor-stability theorem. It does
not establish an identification of these tensor coefficients with
points of a torus, torus-valued scheme cocycle vanishing, or Steinberg
quasi-splitness; those remain separate obligations.
