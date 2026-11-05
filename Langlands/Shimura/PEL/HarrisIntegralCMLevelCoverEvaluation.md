# Restricted raw levels from equivariant finite-etale fibre maps

This internal construction applies the preceding image-fixed raw-level
equivalence to actual finite-etale fibres. The arithmetic fields, central
simple algebra, test schemes and geometric point field are in universe zero.
The abelian family, chosen dual and map to it, full integral order action,
tensor/duality prerequisites, Weil-transition compatibility, adelic
comparison, finite-fibre witnesses, invertible torsion orders and finite-etale
roots of unity are exactly those of the imported raw-level construction.

Let `f : T' ⟶ T` be a morphism of test schemes whose underlying scheme
morphism is finite and etale. Let `s` be the old point and `x` an actual lift
in `Fiber s (cover f.left)`. Both test schemes are quasi-separated. The
old group is the actual `FundamentalGroup s hs`. Its action on the old raw
right-orbit quotient is the existing Weil-frame monodromy action, commuting
with the existing right action and retaining the original Harris level
subgroup convention.

`harrisIntegralCMCoverFiberMapLevel` takes an actual equivariant map from
the full fibre of this cover into the old raw quotient. The image of the new
fundamental group fixes `x` by `fundamentalGroupMap_fixes_lift`.
Equivariance therefore shows that the value at `x` is fixed by that image.
The inverse of `harrisIntegralCMRestrictionImageFixedEquivAt`, with the
propositional point equation `Over.w x`, supplies a fixed raw level on the
direct family over `T'`. Its integral action is literally
`(relativeEndRestrict B f).comp a`.

`harrisIntegralCMCoverFiberMapLevel_val` proves that actual raw evaluation
of this output returns exactly the given map's value at `x`. It uses the
image-fixed equivalence's evaluation formula and its right inverse law.
`harrisIntegralCMCoverFiberMapLevel_injective` assumes that the actual fibre
action is pretransitive. Evaluation at `x` then determines an equivariant
map, by the elementary transitive-action evaluation theorem. The preceding
value formula transfers this uniqueness to the constructed direct level.

The construction needs no connectedness, locally noetherian or algebraically
closed input. Pretransitivity is an explicit hypothesis of the injectivity
theorem only. These results do not assert that all direct levels arise from
equivariant fibre maps: that converse still needs the image of the new
fundamental group to equal the full point stabilizer. They also do not supply
an all-test natural comparison, a normalized PEL moduli representer,
admissibility, smoothness, projectivity or the division representability
theorem. The derivation is entirely internal to the imported actual
finite-etale and raw-level constructions.
