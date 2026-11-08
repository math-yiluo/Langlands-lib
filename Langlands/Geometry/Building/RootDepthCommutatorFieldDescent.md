# Commutator descent from actual collection data

This internal construction works with an arbitrary extension of fields in
universe `u`, an actual smooth affine group `G`, and a monomorphic inclusion
`i` of an original split torus `S`. The supplied upstairs scalar family is
for the actual pullbacks of `S`, `G` and `i`. Only its
`RootDepthCollectionData` are assumed; no full root-datum valuation upstairs
or downstairs is used.

`fieldRestrictedFiltrationSubgroup` is the actual subgroup preimage under
`rationalExtend`, at the original pulled-back character and unchanged real
depth. Its carrier equals the literal `fieldRestrict` filtration for every
nonzero original character. `commutator_le_closure` identifies the supplied
subgroup commutator law with the original closure-of-filtrations formulation.

For original opposite factor pairs and a common positive cocharacter,
`mem_positiveConeGenerated_fieldExtend_iff` reflects the subgroup generated
by the actual positive integral root cone with any additive real depth.
The original finite primitive-positive-root enumeration covers the cone by
primitive roots or their doubles. Character base change transports that
coverage and positivity upstairs. Additivity supplies the combination and
doubled-depth bounds. The previously proved weak-data collection and actual
ordered-factor descent then reflect generated-subgroup membership.

`fieldRestrict_commutator_of_outputDepth` uses this reflection to descend V3
when an additive depth agrees with every actual output depth `p*r+q*s`.
The original input filtration closures extend into the upstairs closures.
The supplied upstairs commutator bound places each extended commutator in
the exact upstairs cone subgroup, and generated-subgroup reflection returns
it to the original cone subgroup. Equality of the generating sets identifies
this subgroup with the literal V3 target. The subgroup commutator universal
property proves the inclusion.

Finally `fieldRestrict_commutator` handles every nonopposite original root
pair and every pair of real depths. Existing split-torus positivity supplies
a common positive cocharacter. The published `exists_additive_outputDepth`
uses rational independence, or the primitive/double classification from
original opposite factor pairs, to supply the required additive output
depth. No positivity of the real depths is required.

The provenance is internal adaptation of `PositiveConeFieldDescent` and
`RootValuationFieldDescent` to the weaker actual collection interface.
All actual character pullbacks, root groups, rational point maps, scalar
families and generating filtrations are retained. This proves V3 under the
stated collection and original geometric hypotheses; reflection V2,
opposite-root V5, initial compatible data and the supplied-model building
comparison remain separate obligations.
