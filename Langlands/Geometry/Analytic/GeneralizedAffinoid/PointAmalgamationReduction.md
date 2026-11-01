# Completed-residue reduction of compatible point amalgamation

Author: Worker 74.

This internal construction uses the published completed residue fields and their
isometric extension maps. It supplies a conditional reduction from
`CompleteFieldAmalgamationStatement` to the published
`PresentedAffinoidAlgebra.PointAmalgamationStatement`. It does not prove the
field-amalgamation hypothesis or the unconditional point or domain assertions.

For a bounded algebra map `g : A → B`, a point `y` of `B`, and a point `x`
of `A` equal to the restriction of `y`, the definition
`BanachSpectrum.completedResidueComapOfEq` maps the completed residue field
of `x` isometrically to that of `y`. The original algebras and coefficient
field may have independent universes, and the original algebras need not be
complete or affinoid. The construction applies `completedResidueLift` to the
composite of `g` and the completed residue evaluation at `y`. The equality of
points supplies the required norm identity on every element of `A`.
`isometry_completedResidueComapOfEq` and
`completedResidueComapOfEq_map` retain the isometry and the commuting
evaluation square.

The theorem
`PresentedAffinoidAlgebra.pointAmalgamation_of_completeFieldAmalgamation`
is proved at the full universe `u`. Given compatible points `x` of `B` and
`y` of `C` over `A`, let `z` be their common restriction. The actual completed
residue fields `H(z)`, `H(x)`, and `H(y)` are complete ultrametric normed
`K`-fields in `Type u`. The published `completedResidueComap` and the new
identified-point variant give an isometric bounded `K`-span
`H(x) ← H(z) → H(y)`.

The hypothesis supplies commuting isometric bounded maps from `H(x)` and
`H(y)` into one complete ultrametric normed `K`-field `L : Type u`.
Composing with the completed residue evaluations gives the required maps
from `B` and `C`. The maps agree on `A` by evaluating the field-span
commuting equation on the image of each `a : A` in `H(z)` and using the
two evaluation squares. The norm identities follow from the output
isometries and `norm_completedResidueMap`.

This is a derived use of the imported constructions and interfaces, not a
transcription of a numbered literature theorem. It retains arbitrary
positive radii, trivial valuations, nonreduced or zero quotients, and empty
spectra as in the point statement. No additional hypothesis on the affinoid
algebras or their points is introduced. The existential field and all maps
remain in the same universe.
