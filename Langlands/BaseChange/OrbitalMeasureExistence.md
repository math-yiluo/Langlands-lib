# Existence of the centralizer and quotient measures

`Langlands.BaseChange.orbitalMeasureExistence` proves
`Langlands.BaseChange.OrbitalMeasureExistenceStatement.{u, v}`. It constructs
the measures on the ordinary and twisted centralizers and their left coset
spaces used in the regular semisimple case of Henniart–Lemaire,
*Changement de base et induction automorphe pour GL_n en caractéristique
non nulle*, Mém. SMF 124 (2011), §§I.2.4–I.2.5, printed pp. 14–17.

## The ambient measures

For `F`, the proof uses `LocalFieldTopology` on `GL_n(F)`. For `E`,
`finiteAlgebraTopology` gives the Hausdorff, locally compact and second
countable topology by using coordinates in a finite `F`-basis. The space of
matrices is a finite power of `E`, and its group of units has the topology
induced by the matrix and its inverse. The ambient groups and their closed
subgroups are second countable and locally compact Hausdorff, so their
locally finite Haar measures are regular. Both ambient Haar measures are
right invariant by `generalLinear_haar_rightInvariant`, using the
modular-character argument for reduced Artinian coefficient rings.

## The ordinary centralizer

The ordinary centralizer is closed because multiplication is continuous
and the group is Hausdorff. The proof takes Mathlib's `Measure.haar` on this
locally compact subgroup. Commutativity for a separable characteristic
polynomial gives right invariance by identifying each right translation
with the corresponding left translation. For any supplied right Haar
measure on this subgroup, `QuotientIntegration.compatibleMeasureExists`
gives a measure on the left coset space compatible with `μF` and that
measure.

## The twisted centralizer

An association witness `x` gives a continuous multiplicative equivalence
from the ordinary centralizer to the twisted centralizer, sending `t` to
`x * baseChange F E n t * x⁻¹`. The pushforward of the supplied right Haar
measure `μγ` along this equivalence is right Haar. The proof composes this
pushforward with conjugation by `x⁻¹` using `Measure.map_map`. The composite
map is coefficient extension, which proves `IsAssociatedMeasure` with
the same witness `x`.

The twisted centralizer is the closed locus where the continuous map
`c ↦ c⁻¹ * δ * entrywiseAut σ n c` equals `δ`. The quotient measure theorem
applies again, with `μE` and the pushed-forward measure. In both cases
the proof uses the left quotient Borel σ-algebra specified by the target.
