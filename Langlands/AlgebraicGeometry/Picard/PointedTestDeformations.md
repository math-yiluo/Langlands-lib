# Actual Picard deformations on arbitrary pointed tests

This is an internal specialization of
`Langlands.CategoryTheory.PseudofunctorPointedDeformations` to the published
`PicardGroupoid.relative` pseudofunctor. Its provenance is the ordinary
line-bundle pullback construction in `Picard.Groupoid`, the relative total-space
functor in `Picard.RelativeGeometry`, and Mathlib's structured-arrow category.
It assumes no external deformation or algebraicity theorem.

## Actual objects and their reduction identifications

Fix any morphism `f : X ⟶ S` of schemes in universe `u`, any object
`T₀ : Over S`, and an actual line bundle `M` on
`(relativeSpace f).obj T₀`. The total space is the chosen fibre product
`T₀.left ×_S X`, canonically isomorphic to the reverse-order product by the
published `relativeSpaceSymmetry`.

A test `T : Under T₀` consists of `T.right : Over S` and a specified arrow
`i_T : T₀ ⟶ T.right` in that slice. `PointedTestDeformations.Deformations f M T`
is the actual structured-arrow category for ordinary pullback along `i_T`.
An object `A` contains an actual bundle `A.right.of` on
`T.right.left ×_S X` and a specified actual isomorphism

```text
M ≅ i_T^*(A.right.of).
```

`reductionIso` exposes this isomorphism, and `mk` constructs an object from
such a bundle and isomorphism. No quotient of objects is taken.

An arrow `a : A ⟶ B` contains an actual bundle isomorphism
`a.right.iso`. `hom_compatibility` states that the chosen reduction
isomorphism of `A`, followed by the pullback of this bundle isomorphism,
is the chosen reduction isomorphism of `B`. `homMk` constructs an arrow
from precisely this compatible isomorphism. `deformationsGroupoid` makes
every arrow invertible: projection to the Picard core reflects isomorphisms,
and all arrows in that core are invertible. The groupoid uses the existing
structured-arrow category and its compatible morphisms.

## Ordinary coherent pullback

For `q : T ⟶ U`, `restrict f M q` is the general restriction construction
specialized to `relative f`. `restrict_obj_bundle` identifies its underlying
bundle with ordinary line-bundle pullback along
`(relativeSpace f).map q.right`. `restrict_map_iso` gives the corresponding
identity on actual bundle isomorphisms.

`reductionComparison f q L` is the actual bundle isomorphism underlying the
component at `L` of the relative pseudofunctor's original `mapComp'`
comparison. It compares direct reduction along `i_U` with reduction along
`i_T` after pullback along `q.right`. The parameter `L` is an object of the
actual Picard core. `restrict_obj_reductionIso` proves the specified formula

```text
reductionIso (restrict q A) = reductionIso A ≪≫ reductionComparison q A.right.
```

`restrictIdIso` and `restrictCompIso` retain the identity and composition
comparisons of the general pointed construction. `pseudofunctor` is its
specialization to the actual relative Picard pseudofunctor on the whole
category `Under T₀`; it includes the proved unit and associativity laws.

## Hypotheses and remaining work

The universe `u` is arbitrary. No properness, flatness, finite presentation,
field, infinitesimal or finiteness hypothesis is imposed. Tests include all
schemes in that universe, including empty, nonreduced and non-quasi-compact
schemes. If `T₀` is a residue-field test, the definition only uses a specified
map from that test; it does not impose a splitting or an algebra structure
over the residue field on the thickening.

This module does not assert an equivalence with the separate dual-number
implementation or a module structure on general deformation classes. Formal
versality, a deformation hull, effectivity, algebraization and openness of
versality are further obligations. In particular it does not prove
`FieldPicardStackAtlasStatement` or produce a smooth scheme chart.
