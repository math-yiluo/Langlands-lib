# Reduction of full-center point quotient compactness

Author: Worker 1232.

`CenterSplitComponentCompactnessReductionStatement.{u}` is a conditional
implication from four existing proposition targets to the unchanged
`CenterSplitComponentCompactnessStatement.{u}`. Its hypotheses are
`CenterMultiplicativeTypeStatement`, `AffineNormalSubgroupQuotientStatement`,
`MultiplicativeTypeSplitQuotientAnisotropyStatement`, and
`AnisotropicCompactnessStatement`, all in the same arbitrary universe.
`centerSplitComponentCompactnessReduction` proves this implication.

For the given connected reductive group `M` over a nonarchimedean local
field, the published full-center existence theorem supplies an actual
closed representative `z : Z → M`. Its structure morphism is affine and
locally of finite type because `z` is closed and `M` is smooth and affine.
The all-test centrality of the split component `i : A → M` gives an actual
factor `j : A → Z`. Closedness of its composite with `z` proves that `j`
is closed, and cancellation through the monomorphism `z` proves centrality.
Its range is therefore normal on every test scheme.

The affine normal-subgroup quotient hypothesis now constructs an actual
affine, locally finite type group `C` and an fppf quotient `q : Z → C`
whose scheme-kernel range equals the full all-test range of `j`. This
uses no smoothness of `Z` or `C`. The proved split-torus local-section
theorem gives `HasOpenSectionsAtPoints` for `q`: its affineness follows
from the affineness of source and target, and the other geometric
conditions come from the fppf quotient.

The first structural hypothesis makes the full `Z` of multiplicative
type. The split-quotient anisotropy hypothesis, applied through its
published center-factor adapter, then supplies
`HasAnisotropicTorusFiniteQuotient C`. Conditional on the anisotropic
compactness hypothesis, the proved finite-quotient compactness theorem
makes the full `C(F)` compact in its canonical rational-point topology.
It uses only attained points of the finite schematic quotient and
retains possible nonsmooth and nonreduced factors.

Finally, `centralPointQuotientModelHomeomorph` uses the actual factorization,
scheme-kernel equality, and constructed open sections to identify the
literal full scheme-center point quotient by the actual image of `A(F)`
with `C(F)`. It uses exactly the inherited center topology and quotient
topology fixed by the target. Transporting compactness through the inverse
homeomorphism gives the target's conclusion.

The provenance is this internal assembly of the published actual-center,
factorization, local-section, finite-quotient, and topology results.
The proof equips the field with the uniform structure associated to its
given topological additive group, so Mathlib can infer the valued-field
separation and open-unit instances. This keeps its given topology.
All four structural hypotheses remain explicit and unproved by this
module. Thus this conditional theorem does not itself prove the
unconditional compactness target or any of its four input propositions.
