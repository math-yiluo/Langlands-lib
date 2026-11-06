# Original completion coordinates and support naturality for curve Weil levels

This derived construction implements the compatibility step in Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed pp.9–10. It concerns the existing original integral Weil model
and original upper integral model, retaining both coefficient bases at
every larger finite support. All fields and schemes share an arbitrary
universe. The arithmetic parameters are finite constants k, the original
rational-function action on K with its compatible k-action, finite K over
the parameter subfield k(s), a nonzero chart denominator t defining the
initial principal support S, and a finite upper extension L/K with the
original compatible constant-field actions. No separability is imposed.

`fieldProjection` is the literal map from an actual enlarged level, over
its original fixed integer base, into any original completed field. It
evaluates the original restricted-product element at that place; even an
outside-support integer coordinate is viewed in its original field.
`fieldProduct` combines all these algebra maps, and its injectivity
follows from equality of every actual restricted-product coordinate.
For any original fixed model Y that is separated over its base and has
quasi-separated underlying space, `point_ext` proves that its level
points are determined by these completed-field coordinates. The source
level ring is reduced because it injects into the product of fields.
The existing separated-scheme coefficient-injectivity theorem then
allows this injection to detect equality of points; the actual product
point map is injective by quasi-separatedness. No finite type or
quasi-compactness assumption is used for this extensionality lemma.

`upperFieldCoefficient` evaluates an original lower level at a specified
lower place and follows the original completion embedding to an actual
upper place above it. Its compatibility theorem states equality of the
two original integral coefficient maps. The proof uses the existing
completion embedding's formula on elements of K. This retains the
original maps from the initial A- and B-integer rings, rather than
replacing them with the rings attached to the enlarged support.

`upperFactorFieldAlgHom` includes each original upper tensor factor in
its original completed field. For a field factor it is the identity; for
an integer factor it is the completed valuation-subring inclusion. The
original upper coefficient formula proves this is a B-algebra map.
`factorPointHomeomorph_left` verifies that the existing regrouping
preserves the underlying actual scheme morphism; its heterogeneous
equality accounts only for the two definitionally branch-dependent
presentations of the same coefficient ring. After splitting into the
field and integer branches, the equality is reflexive.

`localCoefficient` is the original lower level projection followed by
the original lower-to-upper local algebra map. Its compatibility theorem
retains the two original integral bases. Its composition with the
upper factor-to-field inclusion is exactly `upperFieldCoefficient`.
`localPointMap_fieldEvaluation` applies the generic original-counit
evaluation interface: first identify the existing completed-tensor local
counit with evaluation on the whole original lower level, then use upper
coefficient naturality to include the local result into its field.
This step uses local finite type of Y and the existing finite-projective
original integral coefficient extension.

Assume additionally that Y is quasi-compact and quasi-separated and has
a specified relative immersion into finite-dimensional projective space
over its original B. `levelPoint_fieldCoordinate` identifies each upper
completed-field coordinate of the existing enlarged-level Weil
homeomorphism with the original local counit followed into that field.
It uses the proved literal upper projection law, the underlying-morphism
regrouping identity and the original local component law. Spectrum
functoriality combines the upper projection with the integer-to-field
inclusion when needed. `levelPoint_fieldEvaluation` therefore identifies
that coordinate with canonical whole-level evaluation.

`fieldEvaluation` packages the resulting actual Y-point in an upper
completion. `levelPoint_fieldEvaluation_at` indexes its equality with
the upper coordinate by the original lower and upper places, avoiding
any change of meaning as the support varies. Its proof selects the
field or integer branch according to membership in the enlarged support.

`upperTransition` is the literal algebra inclusion between the two
upper full-preimage levels as the lower support enlarges. The proof that
the upper supports are nested uses the actual place-restriction preimage
membership theorem. `upperTransition_pointField` proves that every
original completed-field coordinate commutes with that inclusion by
spectrum functoriality and equality of literal coefficient maps. It
needs no geometric hypotheses on Y. `fieldEvaluation_natural` proves
that the original lower inclusion does not change upper-field
evaluation, by lower coefficient naturality and the literal equality of
the evaluated lower restricted-product coordinates. It needs only local
finite type of Y.

Finally, `levelPoint_natural` proves that the actual fixed-model Weil
homeomorphisms commute with the literal lower and upper support
inclusions. The projective immersion supplies separatedness of Y over
B. The completion-coordinate extensionality lemma reduces the conclusion
to each actual upper place. Restrict that place to K, apply the proved
coordinate/evaluation identification at the two levels, and use the two
coefficient naturality laws above. This proves compatibility of the
constructed maps themselves, without assuming it as a field of an
auxiliary package. Their already established stage topologies are
unchanged. Cofinal assembly into full adelic points and comparison with
the original generic-fiber/spread point spaces remain host obligations.
