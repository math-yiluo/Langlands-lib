# Actual binary norm-one images in the parabolic elementary subgroup

This internal construction combines the actual binary norm-one contractions, actual rational elementary generation criterion, and the proved dynamic-to-geometric-parabolic-radical bridge. Let `k D : Type u`, with `k` a field and `D` a finite-dimensional central simple `k`-algebra, possibly noncommutative. The target `G` is any actual connected reductive group scheme over `k`, and `f : groupScheme k D → G` is any actual homomorphism. Universe and characteristic are unrestricted. No reductivity assumption on the binary source or injectivity assumption on `f` is required.

## Actual elementary images

Fix a finite basis `bD : Module.Basis (Fin d) k D`. As in the imported construction, Boolean `false` denotes the upper elementary family and `true` denotes the lower family. `map_elementaryPoint_mem_parabolicUnipotentPointSet` proves that the image of every actual rational point of either elementary family belongs to the original generator set `parabolicUnipotentPointSet G`. The all-test `elementary_range_le_dynamicUnipotent` puts the elementary point in the source identity-limit subgroup. Dynamic functoriality maps it into the target identity-limit subgroup for the actual composed cocharacter `cocharacter k D neg ≫ f`. The proved `mem_parabolicUnipotentPointSet_of_dynamicUnipotent` then constructs its actual geometric parabolic-radical witness. No parabolicity, radical identification, or structural statement is supplied as a premise.

`map_elementary_range_le_parabolicElementarySubgroup` passes these generators into ordinary subgroup closure. `map_rationalElementarySubgroup_le_parabolicElementarySubgroup` applies preservation of binary suprema by subgroup image. Thus the entire image of `rationalElementarySubgroup k D bD`, the supremum of the two actual rational elementary ranges, lies in `parabolicElementarySubgroup G`. This needs no coefficient SK1 equality.

`rationalElementaryPointsToParabolicElementarySubgroup` restricts the codomain of the original rational point homomorphism on that generated source subgroup. The accompanying coercion identity is reflexivity: its underlying point is exactly `rationalPoints.map f x.val`.

## Full rational images under the explicit coefficient criterion

In the final section `D` is a central division algebra. The hypothesis is precisely

```text
(Reduced.coefficientNorm k D).ker = commutator Dˣ.
```

Here the coefficient norm is the canonical reduced norm on the original units of `D`. `rationalPoints_range_le_parabolicElementarySubgroup` uses the imported exact equivalence `rationalElementarySubgroup_eq_top_iff` with `Module.finBasis k D` to turn this explicit arithmetic equality into generation of all actual binary rational points. Rewriting the preceding image containment by that equality and by `Subgroup.map_top` yields containment of the full original rational image. These full-image results require no basis argument.

`rationalPointsToParabolicElementarySubgroup` is the original full rational point homomorphism with its codomain restricted by that proof. Its coercion identity says that the underlying rational point remains exactly `rationalPoints.map f x`.

`rationalPoints_range_le_parabolicElementarySubgroup_of_iso` extends the full-image result to any actual ground-field model `A` with a specified group-scheme isomorphism `e : A ≅ groupScheme k D` and any actual homomorphism `a : A → G`. Apply the preceding result to `e.inv ≫ a`, and lift each point of `A` through `e.hom`. The two isomorphism maps cancel on the original rational points.

## Provenance and scope

Every construction is an internal consequence of the imported actual scheme morphisms, contracting curves, geometric parabolic/radical proofs, and exact rational generation criterion. The restricted homomorphisms use the original point maps and original parabolic elementary subgroup.

The elementary-image containment is unconditional under the stated field, algebra, and target hypotheses. The full-image containment retains the displayed coefficient SK1 equality as an explicit premise. This contribution does not prove that arithmetic equality over local fields, classify general rank-one groups, prove reductivity of the binary source, or prove the unrestricted `LocalKneserTitsStatement`. Those obligations remain outside this intermediate unit.
