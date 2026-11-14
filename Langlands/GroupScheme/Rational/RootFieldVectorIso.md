# Actual root-field vector isomorphisms

Let a split torus act by conjugation on a smooth affine group over a field `k`.
Fix a nonzero character with no higher positive integral multiples among the
relative roots, and an affine representative `j : U → G` of its intrinsic root
subgroup. Given a field extension `E/k`, a linear equivalence
`W : E ≃ₗ[k] weightSpace i a`, and a finite basis `b` of `E`, this module constructs
an actual group-scheme isomorphism from `U` to the polynomial vector group in
that basis. The field extension can live in an independent universe.

The construction first takes the existing natural weight-vector coordinates of
this representative. Their differential identifies the Lie kernel with a finite
coordinate module. It then corrects those coordinates by the composite of the
inverse differential coordinates, the actual represented-root Lie equivalence,
`W.symm`, and `b.equivFun`. `VectorGroup.linearIso` realizes this correction on
all scheme tests, using mutually inverse coefficient matrices.

`sectionCoordinates_rootFieldVectorIso` proves that on rational sections the
resulting vector is exactly
`b.equivFun (W.symm (rootPointLieEquiv ... (hj.pointsEquiv ... g)))`.
The proof reconciles the identity-test and base-field affine-point conventions
using naturality, applies the linear correction formula, and uses independence
of the representative in the intrinsic root-point Lie comparison.

This is a derived internal comparison for the additive root case of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Appendix C.5.
In particular it can be applied to the existing
`rootOrbitFieldWeightSpaceLinearEquiv`, which defines the rational
`rootFieldCoordinatesOfOrbit` comparison. It does not identify an arbitrary
supplied apartment filtration with this coordinate valuation, and it does not
prove the full special-fibre kernel statement C.5.3.
