# Galois equivariance of the existing geometric CM projective embeddings

Author: Worker 57.

This module proves equivariance of the existing
`cmGeometricProjectiveImmersion` into the specified polynomial projective
space over `AlgebraicClosure F`. Its source is the existing geometric CM
level, and its dimension is the dimension of the specified original map.
The construction keeps the exact `CMRepresentabilityStatement` premise `q`
and every named premise of `HarrisTaylorCMGeometricProjective`.

The arithmetic data are the totally real number field `E`, quadratic CM
extension `F/E`, central simple unitary datum `D`, imaginary quadratic
field `L` mapped to `F`, and specified signature charts `C`, all with
universe-zero carriers. The retained named premises concern pullback tensor
comparison, composition, unit, associativity, left unitor and symmetry;
Picard-zero pullback, Mumford square and universal base change; dual abelian
base-change naturality and polarization stability; relative finite Weil
transition; rational profinite-integer/adele comparison; and torsion finite
etaleness. There is no new coefficient representation, rigidity or
existence hypothesis. The original `SmallCMLevel D` and chosen representation
from the exact `q` are unchanged.

For a level `U` and a specified original map
`i : X_U → ProjectiveSpace F d` over `Spec F`, write `j` for its existing
geometric lift. The map `i` need not be a closed immersion; when it is, the
published instance makes `j` a closed immersion. Write `m_σ,U` for the
existing `cmGeometricGaloisMap σ` at `U`, and `p_σ` for
`ProjectiveSpace.galoisMap F (AlgebraicClosure F) d σ`.
`cmGeometricProjectiveImmersion_galoisMap` proves the actual scheme equation

```text
m_σ,U ≫ j = j ≫ p_σ.
```

The proof applies the generic `ProjectiveSpace.baseChangeLift_galoisMap`
to the existing geometric-level pullback square. The two required source
equations are precisely `cmGeometricGaloisMap_app_projection` and
`cmGeometricGaloisMap_app_structure`. The generic theorem compares the
target's two pullback projections, so no replacement of either scheme or
embedding occurs.

`cmGeometricProjectiveImmersion_galoisAction` applies this identity to
`σ⁻¹` and uses the explicit hom formulas of the existing tower action and
the projective target action. Both left actions use inverse comorphisms.
`cmGeometricProjectiveImmersion_galoisLevelAction` states the same equation
for the existing bundled level action, obtained by evaluating the tower
action. Its proof unfolds that evaluation and uses the preceding theorem.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91, one-based PDF pp.98–99, defines the original
moduli functor and asserts smooth projective representability over the CM
field. III.2, printed pp.96–97, PDF pp.104–105, uses the geometric base change
and the eventual Galois action on cohomology. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's imaginary quadratic `E` is this module's `L`; its `F⁺` is this
module's `E`; its CM field `F` is this module's `F`.

The equivariance identities and the target action are internal
universal-property deductions from the published geometric levels,
projective lifts and Galois maps. They are not additional formulas attributed
to these source pages. The module retains the original existence premise;
it proves neither representability nor continuity of an action, coefficient
equivariance or descent, a cohomological comparison, or completion of the
unitary-geometry task. Only published imported constructions are reused.
