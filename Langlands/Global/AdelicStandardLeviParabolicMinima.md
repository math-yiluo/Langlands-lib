# Intrinsic standard-parabolic minima in the first canonical Levi

Author: Worker 83.

This derived prerequisite identifies the rational comparison groups in
`AdelicStandardLeviHeightRestriction` with the same preceding-intersection
construction applied to actual standard parabolics inside the first canonical
Levi. It then transfers both adapted exact line stabilizers and height minima
to that intrinsic family. It does not complete chamber reduction.

Fix an arbitrary universe `u`, a field `F : Type u`, an affine group scheme
`G` over `Spec F`, a commutative group scheme `T`, a morphism `i : T.toGrp ⟶ G`
and a cocharacter `ν`. Let `K : ℕ → Set (characterLattice T)`, let
`L = Standard.leviScheme i ν (K 0)`, and let `f : L ⟶ G` be its canonical
closed inclusion. The actual lifted torus is
`iL = standardLeviTorusFactor i ν (K 0) (Standard.isRepresentedBy_leviHom ...)`.
The local affine instance for `L` follows from the closed inclusion.

## The intrinsic rational comparison groups

`standardLeviParabolicTailPrefixRationalSubgroup F G T i ν K l` is the existing
`closedPrefixRationalSubgroup` construction in `L`, for its actual canonical
standard-parabolic family indexed by

`K 0 ∩ K (a+1)`.

Thus its `l`th term is the intersection, over `a < l`, of the rational ranges
of `Standard.parabolicHom iL ν (K 0 ∩ K (a+1))`. The empty prefix is the full
rational group. This definition requires no number-field instance, root
validity, reductivity or nesting of the sets `K a`.

For the comparison theorem assume that `G` is connected reductive, `i` is a
maximal split torus, `ν` is generic, and each `K a` is a subset of
`simpleRelativeRoots i ν`. Then
`standardLeviParabolicTailPrefixRationalSubgroup_eq_tail` proves exact
equality with `standardLeviTailPrefixRationalSubgroup`.

The proof first identifies each intrinsic canonical parabolic range with its
standard subgroup-functor carrier. The arbitrary-intersection comparison in
`StandardLeviFamilyRestriction` identifies that carrier with the inverse
image of the ambient `P_(K (a+1))` under `f`. Evaluating on the actual
rational-point test scheme makes its subgroup-functor inverse image exactly
the inverse image under the actual rational-point homomorphism. Taking the
same strict preceding intersections yields the equality. This theorem is
purely algebraic and does not require a number field.

Together with the existing tail comparison, the equality says

`intrinsic_prefix_l = f_F⁻¹(ambient_prefix_(l+1))`.

It does not replace a preceding intersection by a single parabolic.
In the valid reductive setup the published standard-Levi family theorem,
with its structural inputs supplied by `dynamicLie` and
`standardCocharacter`, gives `simpleRelativeRoots iL ν = K 0` and genericity
in the Levi; the published standard-Levi split-component theorem supplies
connected reductivity. Consequently these intersection indices are valid
simple-root subsets in the smaller connected reductive group.

## The same minimum construction in the smaller group

Now assume `[NumberField F]`, and retain the valid reductive setup above.
Take actual representations `ρ_a` on `Fin (d a)`, coordinate indices `j_a`,
and all-test preservation of the coordinate line by the corresponding
ambient canonical parabolics.

For arbitrary `s : ℕ` and `c : ℝ`, suppose an ambient norm-one point `p`
satisfies the first `s+1` minimum inequalities over the ambient preceding
intersections. Supply separately a norm-one point `m` of `L`, an adelic
point `x` of the first canonical unipotent subgroup, and the ordered equality

`p = image(m) image(x)`.

`mem_chainHeightMinimalSet_standardLevi_parabolicTail` puts `m` in the
existing `chainHeightMinimalSet` for the first `s` members of the intrinsic
parabolic family, with the restricted representations `ρ_(a+1)|_L`,
the coordinate vectors `e_(j_(a+1))`, and the unchanged constant `c`.
Its conclusion explicitly uses `closedPrefixRationalSubgroup` for the
canonical intrinsic parabolic schemes and morphisms. The proof applies the
existing unipotent-factor tail transfer and rewrites its rational comparison
family using the proved function equality.

`standardLevi_parabolicTail_exactStabilizers_and_minima` strengthens the
representation input to an exact ambient stabilizer on every scheme test,
using a unit of its ring of global sections. It concludes both the exact
intrinsic stabilizers for all restricted successor representations and
the same intrinsic minimum inequalities. The first conclusion applies the
all-test coordinate-line restriction theorem for each successor index.
For the second, each exact ambient stabilizer supplies line preservation
by evaluating at a point composed with its canonical parabolic inclusion.
The preceding minimum-transfer theorem then applies.

No faithfulness, splitness of `G`, nonempty root set, nesting of `K a`, or
positivity of `c` is required. The case `s=0` is included. The stronger exact
stabilizer condition is used only in the final combined theorem.

## Provenance and scope

This is an internal consequence of the two imported Library interfaces,
using their implemented subgroup functors, actual canonical representatives,
actual rational-point maps, restricted representations and height minima.
It introduces no further assertion from external literature. The structural
comparison uses the proved arbitrary-intersection restriction; the height
argument uses the proved canonical unipotent-factor restriction.

The factorization and norm-one membership of `m` remain explicit inputs.
Neither follows here from ambient norm-one membership. This module does not
construct such factors, compare line characters with simple roots, prove
rank-one height bounds, carry out rank induction, or establish
`AdelicSiegelChamberReductionStatement`.
