# Hausdorff adelic points of separated field schemes

`Langlands.Global.AdelicSpreadSeparatedStatement` conjoins Hausdorffness of
actual adelic points in the two arithmetic settings. The topology is the
previously defined topology of an explicitly specified finite-type arithmetic
spread. Separatedness is imposed on the scheme over the original field.

For each finite set `S`, the model `M` is over the actual integer ring outside
`S`, with `LocallyOfFiniteType M.hom` and `QuasiCompact M.hom` expressing
finite type. A specified isomorphism identifies its actual generic fiber with
the field scheme `Y`. The conclusion is `T2Space` for the actual relative
scheme points `CurvePlaceAdelePoints k F Y` or `NumberFieldAdelePoints K Y`,
with exactly `curvePlaceSpreadAdelePointTopology` or
`numberFieldSpreadAdelePointTopology`. Those topologies transport the existing
arithmetic-stage final topology; no separation or topology comparison is
assumed in their definitions.

The premise is `IsSeparated Y.hom`. No separatedness, affineness, or group
structure is imposed on the model, and `Y` need not be affine. The function-field
clause retains arbitrary perfect constants, the specified rational-function
scalar action and scalar tower, and potentially inseparable extensions. It
requires no finite constant field or local compactness hypothesis. The
number-field clause includes every infinite factor. Empty finite place sets
are allowed. Existence of a model or its generic-fiber isomorphism is not
asserted; they are explicit inputs.

## Source and derived scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed
p.9, Section 4, asserts Hausdorffness for separated finite-type schemes over
global fields with the final adelic topology. Finite type of `Y` here follows
from finite type of `M`, generic-fiber base change, and the given isomorphism.
The finite-constant specialization and the number-field clause express that
source assertion for a specified spread. Its extension to arbitrary perfect
constants is derived and concerns Hausdorffness alone.

The derived route avoids requiring a separated spread: construct the
finite-type model product `M ⨯ M` and its generic-fiber isomorphism to
`Y × Y`. The independent-spread product comparison identifies its actual point
space with the product of the two original point spaces. Separatedness of
`Y` makes its field-scheme diagonal a closed immersion, so the independent-spread
closed-immersion property makes its point map a closed embedding. Under the
product comparison its image is the ordinary diagonal. The closed-diagonal
criterion therefore gives Hausdorffness of precisely the original topology.

`AdelicSpreadTopologicalPropertiesStatement` gives a distinct intermediate
Hausdorff clause under separation of the arithmetic model; the present target
supplies separation over the field for arbitrary chosen models. The product
and closed-immersion interfaces and this target have separate proof obligations.
This pair supplies a proposition interface, without its proof, a
model-existence theorem, or whole-paper completion.
