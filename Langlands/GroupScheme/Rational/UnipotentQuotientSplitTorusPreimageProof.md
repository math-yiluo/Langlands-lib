# Proof: the preimage of a split subtorus under a unipotent quotient

This module proves the published statement
`Langlands.GroupScheme.UnipotentQuotientSplitTorusPreimageStatement.{u}` by the
theorem `Langlands.GroupScheme.unipotentQuotientSplitTorusPreimageStatement`.
The statement and its Markdown are in
`Langlands.GroupScheme.Rational.UnipotentQuotientSplitTorusPreimageStatement`;
it is the inverse-image step of the proof of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, Theorem C.2.3.

The module also contains one auxiliary theorem,
`UnipotentQuotientSplitTorusPreimage.isSolvable_preimage_points`.

## Auxiliary theorem

`isSolvable_preimage_points` works over a field `k` with group schemes
`G U Q`, a homomorphism `r : U ⟶ G`, a homomorphism `q : G ⟶ Q`, a commutative
group scheme `B` and a homomorphism `z : B.toGrp ⟶ Q`. It assumes that
`U.X.hom` is affine and locally of finite type, `IsUnipotent U`,
`IsFppfQuotient (SubgroupFunctor.range r) q` and `IsClosedSubgroup z`. It
concludes that for every scheme `T` over `Spec k`, the group of `T`-points of
the actual inverse image `SubgroupPreimage.groupScheme q z` is solvable.

## The implemented proof

The witness is the actual inverse image `H := SubgroupPreimage.groupScheme q z`
(the group-scheme pullback of `z` along `q`) with its inclusion
`j := SubgroupPreimage.inclusion q z` into `G`.

Instances. From the hypotheses: `r` and `z` are closed immersions; `q` is flat,
surjective and locally of finite presentation (the first three clauses of
`IsFppfQuotient`); `U.X.hom` is affine because it is the composite of the closed
immersion `r` with the affine `G.X.hom`; `Q` is separated over the field
(`fieldSeparated`), so `q` is quasi-compact (`QuasiCompact.of_comp`, since
`q ≫ Q.X.hom = G.X.hom` is affine). The range of `r` is represented by `r`
(`r` is a monomorphism over the base, by `Over.mono_of_mono_left`), so the
Library's `IsFppfQuotient.smooth_of_smooth_kernel` makes `q` smooth. The
split torus `B` is smooth and connected (`IsSplitTorus.smooth`,
`IsSplitTorus.connectedSpace`).

Closed, smooth and affine. `SubgroupPreimage.isClosedSubgroup`,
`SubgroupPreimage.smooth` (using smoothness of `q` and of `B`) and
`SubgroupPreimage.isAffineHom` give the first three properties of `H`.

Connected. `U` is geometrically connected by the Library's
`geometricallyConnected_of_connected`. `IsFppfQuotient.kernelIso` identifies
`U` with the actual kernel of `q`, and geometric connectedness transfers along
this isomorphism (`MorphismProperty.cancel_left_of_respectsIso`). The pullback
square `SubgroupPreimage.isPullback_scheme` shows that the underlying set of
`H` maps homeomorphically (closed embedding) onto `q⁻¹(range z)`. The range of
`z` is connected and closed, so `FppfQuotientGeometry.isConnected_preimage`
makes this inverse image connected, and
`FppfQuotientGeometry.connectedSpace_of_isEmbedding` makes `H.X.left`
connected.

Solvable. By the Library's `isSolvableGroupScheme_of_isSolvable_points` it
suffices that the points of `H` over the algebraic-closure point are a solvable
group; `isSolvable_preimage_points` gives this for every test scheme `T`. In
its proof, let `p : H(T) →* B(T)`, `incl : H(T) →* G(T)` and
`ρ : U(T) →* G(T)` be postcomposition (`IsMonHom.monoidHom`). `B(T)` is
commutative, hence solvable. For `x` in the kernel of `p`, the pullback square
gives `incl x ≫ q = 1`, so `incl x` lies in the range of the actual kernel
inclusion, which by the kernel clause of `IsFppfQuotient` equals the range of
`ρ`. Since `incl` is injective (the inclusion is a closed immersion, hence a
monomorphism), `ker p` embeds into `ρ.range`, a quotient of `U(T)`. The group
`U(T)` is nilpotent by the Library's `isNilpotent_points_of_isUnipotent`
(`Rational.UnipotentPointsNilpotent`), hence solvable, and so is its quotient
`ρ.range`. Hence `H(T)` is an
extension of a subgroup of the solvable `B(T)` by the solvable `ker p`.

Factorization. Given `i : K ⟶ G` and `g : K ⟶ B` with `g ≫ z = i ≫ q`, the
pullback lift `pullback.lift i g` is a homomorphism `K ⟶ H` whose composite
with `j` is `i` (`pullback.lift_fst`).

## Provenance

The argument follows the inverse-image step of CGP Theorem C.2.3: the preimage
of a torus under a quotient by a smooth connected unipotent subgroup is smooth,
connected and solvable. The helper unit `FppfQuotientGeometry`, submitted with
this proof, supplies the connectedness of inverse images; the nilpotence (hence
solvability) of unipotent point groups is the Library's
`isNilpotent_points_of_isUnipotent`. All other ingredients are cited above by
their Library or Mathlib names. One tactic is run with
`set_option backward.isDefEq.respectTransparency.types false`, as in the
Library's `GeometricConnectedness`, so that the `RespectsIso` instance for
`GeometricallyConnected` is found.

Worker 1390 authored this proof.
