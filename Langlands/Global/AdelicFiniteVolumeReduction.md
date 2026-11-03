# Reduction of finite volume to the connected reductive case

This module reduces the finite-volume target
`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement` (Library
module `Langlands.Global.AdelicFiniteVolumeStatement`) to three separate Prop-valued
statements. It proves the implication and proves none of the three inputs, so it does not
prove the target itself.

## Statement

`NormOneFiniteVolumeReductionStatement` is the Prop-valued implication, at universe `u`,

    CharacteristicZeroLeviDecompositionStatement →
      UnipotentTriangularCoordinatesStatement →
        ConnectedReductiveFiniteVolumeStatement →
          NormOneRationalQuotientFiniteVolumeStatement

and `normOneFiniteVolumeReductionStatement` proves it. The four propositions are existing
Library declarations, used unchanged:

* `Langlands.GroupScheme.CharacteristicZeroLeviDecompositionStatement`
  (`Reductive.CharacteristicZeroLeviStatement`): every smooth connected affine finite-type
  group scheme `G` over a field of characteristic zero has homomorphisms `p : G ⟶ L`,
  `j : L ⟶ G` with `j ≫ p = 𝟙 L`, `L` connected reductive, and `GroupScheme.kernel p`
  smooth, connected and unipotent.
* `Langlands.GroupScheme.UnipotentTriangularCoordinatesStatement`
  (`GroupScheme.TriangularCoordinates`): every smooth connected unipotent affine finite-type
  group scheme over a field of characteristic zero has triangular polynomial coordinates
  (`HasTriangularCoordinates`).
* `Langlands.Global.AdelicGroupPoints.ConnectedReductiveFiniteVolumeStatement`
  (`Global.AdelicReductiveFiniteVolumeStatement`): `normOneRationalQuotientHaarMeasure F G`
  is finite for every connected reductive `G` over a number field `F`.
* The target, which asserts the same finiteness for every affine finite-type `G` over a
  number field with `G.X.hom` smooth and `G.X.left` connected.

The quotient measure is the same in the target and in the reductive input: the quotient of
the fixed Haar measure on `G(𝔸_F)¹` by counting measure on the principal subgroup. The
module changes no convention and adds no hypothesis to the target.

## Supporting theorem

`isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi` proves finiteness of
`normOneRationalQuotientHaarMeasure F G` for a fixed number field `F` and a fixed smooth
connected affine finite-type `G`. Its premises are the Levi statement, the unipotent
compactness statement `UnipotentRationalQuotientCompactStatement` (compactness of
`RationalQuotient F U` for smooth connected unipotent `U`, module
`Global.TriangularRationalQuotientCompact`) and the reductive statement.

## Proof

For `isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi`:

1. The Levi statement, applied to `F` (characteristic zero as a number field) and `G`, gives
   `L`, `p`, `j` with `j ≫ p = 𝟙 L`, `IsConnectedReductive L`, and the smoothness,
   connectedness and unipotence of `U = GroupScheme.kernel p`.
2. The instances on `L` needed below come from `IsConnectedReductive L`. Its field
   `isAffineHom` and Mathlib's `isAffine_of_isAffineHom` (the base `Spec F` is affine)
   give `IsAffine L.X.left`. Its field `smooth` gives `Smooth L.X.hom`, and from it Mathlib
   derives `LocallyOfFiniteType L.X.hom`.
3. The published `kernel_isAffine F p` and `kernel_locallyOfFiniteType F p` (module
   `Global.AdelicLeviFiniteVolume`) give the affine and finite-type instances on `U`.
4. The unipotent compactness statement, applied to `U`, gives compactness of
   `RationalQuotient F U`. The reductive statement, applied to `L`, gives finiteness of
   `normOneRationalQuotientHaarMeasure F L`.
5. The published `leviReductionFiniteVolumeStatement` (the proof of
   `LeviReductionFiniteVolumeStatement`) applied to `F`, `G`, `L`, `p`, `j`, the section
   identity and these two facts gives finiteness of `normOneRationalQuotientHaarMeasure F G`.

`normOneFiniteVolumeReductionStatement` turns the triangular-coordinate premise into the
unipotent compactness premise with the published
`unipotentRationalQuotientCompact_of_triangularCoordinates`, and then applies the
supporting theorem to each `F` and `G` quantified in the target.

## Provenance

The reduction is internal to this project. It assembles published Library results and adds
no mathematics of its own. It follows the standard route to Borel–Harish-Chandra finite
volume through a Levi decomposition `G = U ⋊ L`. The sources of the three inputs are cited in
their own modules: Milne, *Algebraic Groups* (2017), 25.48–25.49 for the Levi decomposition;
Milne 14.32 and 14.34–14.36 for the triangular coordinates; Getz–Hahn (2024), Theorem 2.6.3
for the reductive case. The target is Getz–Hahn's Theorem 2.6.3 over number fields, as
recorded in the Markdown of `AdelicFiniteVolumeStatement`. Getz–Hahn do not prove the theorem
through this route, and this file attributes the route to no particular source.
