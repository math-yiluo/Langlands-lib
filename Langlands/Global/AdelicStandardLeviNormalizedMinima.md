# Constructing norm-one minima in the first standard Levi

Author: Worker 83.

This derived prerequisite removes the separate norm-one premise on the
initial Levi factor in the canonical height-minimum restriction step. It
extracts an actual positive factor in a constructed split component and
proves that the resulting norm-one Levi point satisfies the same successor
minimum inequalities over the intrinsic preceding standard parabolics.

Fix an arbitrary universe `u`, a field `F : Type u`, an affine group scheme
`G` over `Spec F`, a commutative group scheme `T`, a morphism
`i : T.toGrp ⟶ G` and a cocharacter `ν`. For
`K : ℕ → Set (characterLattice T)`, write `L` for the actual first canonical
Levi `Standard.leviScheme i ν (K 0)` and `f : L ⟶ G` for its canonical
inclusion. The local affine instance for `L` comes from this closed inclusion.
The height and normalization constructions require `[NumberField F]`.

## The normalized conclusion

`HasNormalizedStandardLeviTailMinima F G T i ν K s d ρ j c h` is a
proposition about an arbitrary actual adelic point `h` of `L`. It asserts
the existence of an actual commutative group scheme `A`, morphisms
`z : A.toGrp ⟶ L` and `b : A.toGrp ⟶ T.toGrp`, with

`IsSplitComponent z` and `b ≫ i = z ≫ f`,

and points

`a ∈ PositiveRealTorus.intrinsicSubgroup F A`,

`m ∈ normOneSubgroup F L`,

such that `positivePointMap(a) m = h` in the actual adelic group of `L`.
The point `m` satisfies the first `s` inequalities in the existing
`chainHeightMinimalSet` for the successor representations `ρ_(a+1)|_L`,
coordinate vectors `e_(j_(a+1))`, and
`standardLeviParabolicTailPrefixRationalSubgroup`, with unchanged real
constant `c`. The latter comparison groups are the actual intrinsic
preceding parabolic intersections, indexed by `K 0 ∩ K (a+1)`.

No character-norm condition on the original `h` occurs in the definition.
The constructed `m` is an additional factor; its norm-one condition is not
inferred for the original `h`.

## Restriction before normalization

`mem_adelicChainHeightMinimalSet_standardLevi_tail` assumes connected
reductivity of `G`, maximal splitness of `i`, genericity of `ν`, and validity
of every `K a` as a subset of `simpleRelativeRoots i ν`. Take an arbitrary
family of actual representations with selected coordinate lines preserved,
on every scheme test, by their individual ambient canonical parabolics.

Suppose a raw ambient adelic point `p` satisfies the first `s+1` full
adelic minimum inequalities over the preceding ambient parabolic
intersections, and supply an ordered equality

`p = image(h) image(x)`,

where `h` is an arbitrary adelic point of `L` and `x` is an adelic point
of the corresponding canonical unipotent subgroup.
The theorem proves the first `s` full adelic inequalities for `h`, the
successor restricted representations, and the pulled-back tail comparison
groups, with the same `c`. Neither `p` nor `h` is required to be norm one.

The proof applies the full adelic fixed-factor restriction theorem. The
canonical unipotent group is unipotent and fixes the retained coordinate
vectors because it preserves their lines. The canonical Levi image
normalizes it. The exact shifted-prefix pullback gives comparison-group
containment, and principal-point naturality supplies the normalizer
condition after each rational test.

## The split component preserves every selected line

`preservesCoordinateLine_standardLevi_of_torus_factor` is purely algebraic.
For arbitrary index sets `J,K`, a morphism `z : A ⟶ L_J` whose ambient
composite factors through `i` inherits preservation of a supplied
`P_K`-adapted coordinate line. No reductivity, root validity or splitness
premise is needed for this helper.

On every scheme test, the composite point belongs to the torus range,
which lies in `L_K` and hence in `P_K`. Canonical representability factors
the point through the actual `P_K` representative. The supplied line
preservation and the actual representation-restriction identities give the
required scalar action. All scalars remain global units on the same test.

## Constructing the norm-one factor

`hasNormalizedStandardLeviTailMinima_of_factor` has the valid reductive
setup and line-preservation assumptions of the raw restriction theorem.
It takes an ambient norm-one point `p` satisfying the first `s+1` existing
norm-one minimum inequalities, together with the displayed ordered
Levi-unipotent factorization. Its initial Levi factor `h` is an arbitrary
adelic point, with no separate norm-one premise.

The proof first restricts the inequalities to `h`. The published
`standardLeviSplitComponentStatement` supplies connected reductivity of
`L`, an actual split component `z : A.toGrp ⟶ L`, and its factorization
through the fixed ambient torus. The purely algebraic helper supplies
line preservation along `z` for every retained restricted representation.
The actual split-component normalization theorem then constructs `a,m`
and their equality, preserving all the inequalities with the same `c`.
Finally the proved intrinsic-prefix/tail equality rewrites the comparison
groups into the intrinsic standard-parabolic construction.

The constant `c` is any real number; `s=0` is included. No nesting of
`K a`, faithfulness, splitness of `G` or nonempty-root premise is added.
Exact stabilizers, when available, restrict independently by the imported
all-test canonical-Levi comparison.

## Provenance and remaining obligations

This is an internal consequence of the two imported height interfaces and
their proved structural inputs. It introduces no new assertion from
external literature. Its new conclusion constructs the norm-one factor
instead of imposing all Levi character-norm conditions on a supplied one.

The original Levi-unipotent factorization is still an input. This module
does not establish bounds on simple-root norms, prove rank-one reduction,
carry out rank induction or establish
`AdelicSiegelChamberReductionStatement`.
