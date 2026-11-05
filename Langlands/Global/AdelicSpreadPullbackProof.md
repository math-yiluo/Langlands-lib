# Field-level adelic pullbacks from independent spreads

`Langlands.Global.adelicSpreadPullback` proves exactly
`Langlands.Global.AdelicSpreadPullbackStatement` at arbitrary common universe
`u`. Its two clauses are `curvePlaceSpreadPullback` and
`numberFieldSpreadPullback`. Both use the actual full-adele scheme points and
the specified arithmetic-spread topologies. The field base is separated;
neither factor nor the pullback vertex is assumed affine or separated.
There is no arithmetic model or finite-type premise on the field base.

## Categorical and point-topology argument

For a limiting pullback cone and any specified limiting binary fan, the private
`pullbackToProduct` is the product universal-property map. Its compositions
with the product projections are the pullback legs. The fork with this map is
an equalizer of the two product-to-base composites: lift any equalizing arrow
using the pullback limit, then verify uniqueness with the product and pullback
limit properties. The unique isomorphism to Mathlib's chosen equalizer
expresses the map as an isomorphism followed by the equalizer inclusion.
`AlgebraicGeometry.isClosedImmersion_equalizer_ι_left` gives the closed immersion
because the field base structure map is separated.

The private point-topology helper takes the product comparison homeomorphism
and an embedding for this pullback-to-product map. Their composition is an
embedding into the ordinary factor product. The two leg identities identify
it with the cone-leg point map followed by the inclusion of the compatible-pair
subtype. Since that inclusion is an embedding, the cone-leg map is an embedding.
`affineSchemePullbackPointEquiv` supplies its surjectivity onto the compatible
pairs. Mathlib's embedding-and-surjectivity criterion gives the homeomorphism.
This point equivalence uses the scheme pullback universal property and has no
affineness hypothesis despite its historical name.

## Arithmetic specialization

In each arithmetic case, enlarge the two factor model bases to `S ∪ T`. The
canonical iterated-base-change isomorphisms identify their generic fibers with
the original factors. Take their actual product over the common integer base;
its structure map is finite type, by base change on a projection and composition.
This reuses `finiteType_overProd` and the two generic-fiber composition
isomorphisms from `AdelicSpreadProductProof`. No separatedness premise is
needed for this step. Generic-fiber pullback
preserves the binary product, and composing its legs with the factor
isomorphisms gives a limiting field product. This product is already the generic
fiber of the constructed product model, so its spread isomorphism is identity.

Apply `adelicSpreadProduct` using the original independent factor spreads and
this new product spread. Apply `adelicSpreadClosedImmersion` using the
independently specified pullback-vertex spread and the product spread. Its
closed embedding supplies the embedding required by the general point-topology
helper, which proves the exact compatible-pair comparison.

The function-field clause retains arbitrary perfect constants, the specified
rational-function scalar action and tower, and possibly inseparable finite
extensions. The number-field clause retains every infinite factor in the full
adeles. Empty finite sets are allowed, and no local compactness or
finite-residue-field premise is added.

## Provenance and dependencies

This is a derived proof of the published separated-base target, associated
with Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
pp.8–9, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
as explained in the target Markdown. It uses the published target and
the independent-spread product and closed-immersion proof modules; it does not
claim an unrestricted nonseparated-base comparison. The categorical proof
route is internal and need not follow Conrad's argument verbatim.

Worker 208 authored the proof and original explanation. Worker 1592 verified
the pair against the published dependencies and prepared this proof-only
submission. All predecessor results are imported by Lean name from the Library.
