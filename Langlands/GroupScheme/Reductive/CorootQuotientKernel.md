# Full kernels of supplied split coroot quotients over fields

Let k be any field, G a connected reductive group scheme over k, and
`t : splitTorus (Spec k) I ⟶ G` an actual maximal torus with monomorphic
underlying scheme morphism. The coordinate type I is finite and has decidable
equality. Let P be a root datum on the full coordinate lattices `I → ℤ`, whose
field realization is an actual root datum of t. Suppose a homomorphism
`q : G ⟶ (corootQuotient k P).toGrp` restricts on t to `corootProjection k P`.

The module proves `isDerivedSubgroup_kernelι_of_corootProjection`: the full
scheme kernel of q, with its actual inclusion, is the scheme-theoretic derived
subgroup of G. Consequently `isSemisimple_kernel_of_corootProjection` proves
that this full kernel is semisimple. Neither smoothness nor surjectivity of q
is an additional premise. The result holds uniformly in the universe u.

The construction `corootQuotientKernelIsoDerived` compares this actual kernel
with any supplied actual derived subgroup of G. It applies the published
isomorphism between two representations of the same all-test subgroup functor.
Thus it compares group schemes over k, rather than only abstract groups of
field-valued points.

The proof uses the following character comparison.

- `corootProjection_comp_evalCharacter` proves on every relative test scheme
  that evaluation on an annihilating character pulls back to its exponent
  character on the coordinate torus.
- `characterRestrict_mem_cocenterLattice` uses the published fact that actual
  coroots land in every closed subgroup containing all commutators. The actual
  derived subgroup is such a subgroup. Every ambient rational character kills
  it, so its restriction annihilates all coroots. The actual root-datum pairing
  and the coordinate field realization identify this with membership in the
  coroot-annihilator lattice.
- `hom_ext_of_epi_subgroupProductMap` compares homomorphisms by their
  restrictions to two subgroup schemes whose product map is an epimorphism.
  It uses preservation of multiplication, with no commutativity assumption
  on the target. `character_factors_corootQuotient` applies this to the actual
  derived subgroup and t: each ambient character factors through q by an
  evaluation character of the coroot quotient.

For the full-kernel equality, choose an actual derived subgroup using the
published representability theorem. Its product with t is scheme-surjective;
smoothness of G makes this product an epimorphism. The published affine normal
quotient gives a smooth affine commutative quotient C by that subgroup. The
map from t to C is surjective, so C is split. Every character of C, pulled back
to G, factors through q by the preceding comparison. Therefore every all-test
point killed by q maps to the identity of C: actual characters separate all-test
points of the split torus C. The full-kernel clause of the represented fppf
quotient places this point in the actual derived subgroup. Conversely, the
published derived-subgroup annihilation theorem applies to q because its
actual target is affine and commutative. These two inclusions identify the
entire all-test kernel range with the derived subgroup. The published field
semisimplicity theorem then applies to the actual kernel inclusion.

This is an internal consequence of the imported character, derived-subgroup,
quotient and root-datum APIs. The coroot quotient and its projection are the
separate constructions of `CorootTorusQuotient` and `CorootTorusProjection`,
used here unchanged.
The module does not construct q. Specialization to geometric fibres over an
arbitrary coefficient ring, and the unconditional relative existence theorem
for a semisimple normal subgroup with torus quotient, are not part of this
module.
