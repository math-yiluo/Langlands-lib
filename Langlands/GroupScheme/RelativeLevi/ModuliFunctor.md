# The relative Levi moduli presheaf

`RelativeLevi.moduliFunctor P` is a presheaf on the category of schemes over
`S : Scheme.{u}` for any group scheme `P` over `S`. Its value on `T → S` consists
of the all-test subgroup images of actual inclusions `L → P_T` satisfying
`IsRelativeLeviSubgroup`. Equality is equality of subgroup functors. All
geometric objects remain in universe `u`, with presheaf values in `Type (u+1)`.

The published `smoothAlgebraicallyClosedUnipotentRadicalExtension` discharges
the field-extension premise of `ModuliFieldReduction`. A Levi presentation
supplies the ambient smoothness needed there. Consequently
`IsRelativeLeviSubgroup.baseChange` preserves the given inclusion under any
base morphism, and `restrictionStable` proves that every restriction of a Levi
image is a Levi image. `moduliFunctor_map_val` identifies the restriction on
images with `restrictImage`, which uses the actual ambient pullback comparison.
The functor inherits the established identity and composition laws.
`moduliInclusion` forgets the Levi condition and retains the subgroup functor.

For `r : U → P`, `leviConjugationAction r T` is the action of the group of
`T`-points of `U`. It sends a Levi image to its conjugate by the image of the
point under `r`, viewed as a point of `P_T`. In particular this defines the
action for a supplied relative unipotent radical. `moduliFunctor_map_smul`
shows that restricting a conjugate gives the conjugate of the restriction
by the restricted group point.

`ModuliRepresentation.representableBy` interprets the correspondence in the
published torsor statement as a `Functor.RepresentableBy` for `moduliFunctor P`.
It uses the same point equivalences and obtains their naturality as an
equality of Levi images from their underlying subgroup-functor equality.
`ModuliRepresentation.representableBy_equivariant` gives equivariance for
this conjugation action from the `IsEquivariant` condition of the torsor
conclusion.

This module is an internal composition of the published field-extension proof,
the field reduction, and the existing restriction, conjugation, and
representation interfaces. In the parabolic setting, Conrad's
*Reductive group schemes* (2014), Definition 5.4.2 (p. 174) and Corollary 5.4.6
(p. 178), give the original definition of `Lev(P)` and its radical action.
The source comparison is recorded in
[ModuliValue.md](ModuliValue.md) and [TorsorStatement.md](TorsorStatement.md).
