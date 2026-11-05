# Projective embeddings of the existing geometric CM levels

This module constructs projective-space embeddings of the already defined
`cmGeometricOverTower`, and proves its structure morphisms proper over
`AlgebraicClosure F`. All conclusions retain the exact
`CMRepresentabilityStatement` premise `q`.

The arithmetic input is the same as for `HarrisTaylorCMGeometricCoefficients`:
the totally real number field `E`, quadratic CM extension `F/E`, central simple
unitary datum `D`, imaginary quadratic field `L` mapped to `F`, and the
specified signature charts `C`. The named tensor comparison, composition,
unit, associativity, unitor and symmetry premises, Picard pullback, Mumford
square, universal base change, duality naturality, polarization stability,
finite Weil transition, rational profinite-integer/adele comparison and torsion
finite-etaleness premises are retained. The levels are the original
`SmallCMLevel D`. There are no additional coefficient representations,
dual-existence or coarse-rigidity hypotheses in this module.

For a fixed level `U`, a dimension `d`, and an actual original map
`i : X_U → ProjectiveSpace F d` over `Spec F`,
`cmGeometricProjectiveImmersion` is the lift through the polynomial
projective-space base-change square. Its domain is exactly the existing
geometric level `X_U ×_{Spec F} Spec (AlgebraicClosure F)`.
The `toSpec` and `map` theorems prove its two projection equations. The
`isPullback` theorem identifies it as the actual base change of `i`; the
closed-immersion instance follows when `i` is a closed immersion.
The dimension remains `d`.

`cmGeometricOverTower_projective` applies the reusable construction in
`ProjectiveSpace.BaseChange` to the projective witness of the original
`chosenCMLevelRepresentation` selected from `q`. It proves
`IsHProjective` for the structure morphism of the existing geometric level.
`cmGeometricOverTower_isProper` composes this closed immersion with the proper
structure morphism of finite projective space.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91, one-based PDF pp.98–99, defines the sufficiently
small levels and the original moduli functor, and asserts smooth projective
representability over the CM field. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The implemented base-change embeddings and properness are internal deductions
from the exact representation witness and the published polynomial-Proj
base-change and properness results. They are not a proof of the original
representability assertion.

The general datum still needs an applicable existence theorem and the
remaining canonical-model, cover and coefficient-descent prerequisites.
This focused construction does not complete the host task.
