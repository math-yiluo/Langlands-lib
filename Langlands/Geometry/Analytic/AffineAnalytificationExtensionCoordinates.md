# Algebraic coordinates of extension-field-valued affine analytic points

This internal unit recovers algebraic coordinates from full field-valued points
of the constructed affine analytification over `K`, with values in an arbitrary
normed extension `L`. It retains the actual evaluation characters. No
completeness, algebraic closedness, or finite-degree hypothesis on `L` is used.

## Restricting the constructed saturation

`FieldPoint.restrictSaturation` restricts a full `L`-valued point of a constructed
saturation to the original atlas. For each original chart, its whole domain is
an index of the saturated atlas. The saturated-to-original inclusion supplies a
bounded map from the original chart algebra to the chosen saturated algebra.
Composing its pullback with the full point's evaluation gives the original
character. Naturality of this inclusion gives the original chart point and its
norm identity.

For nested original charts, the two inclusion composites agree because
local-domain inclusions form a thin category. Their bounded restrictions
therefore agree. Combined with the saturated evaluation compatibility, this
gives compatibility of the recovered original evaluations. The construction
preserves the underlying point exactly and applies to arbitrary independent
universes for the base field, value field, atlas space and chart indices.

## Affine algebraic coordinates

`originalExtensionAlgHom` takes an `L`-valued point of the original polynomial
atlas, chooses a chart through it, and composes the chart character with the
coordinate-algebra map from `A`.

`originalExtensionAlgHom_apply_eq` proves that every containing chart computes
the same map. Two such charts have a common smaller polydisc through the point.
Evaluation compatibility and the polynomial-locus restriction formula identify
both computations with the evaluation in that smaller chart.

`extensionAlgHom` applies this construction after `restrictSaturation`. Thus a
full `L`-valued point of the saturated affine analytification gives an actual
`K`-algebra map `A → L`. `norm_extensionAlgHom` states that its absolute values
equal the published algebraic point seminorm of the underlying analytic point.
The proof computes in a containing chart and uses the defining chart-character
norm identity.

This unit does not prove a full comparison bijection over `L` or Galois descent.

## Provenance

This is an internal deduction from the published constructed saturation,
local-domain inclusion category, all-chart `FieldPoint` data, polynomial-locus
coordinate-algebra maps and restriction formulas, and algebraic point seminorm.
The common-polydisc coordinate argument generalizes the published
`toAlgPoint_apply_eq` from the value field `K` to `L` without changing its proof.
