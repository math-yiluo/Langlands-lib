# Original completion evaluation and support naturality for number-field Weil levels

This derived unit supplies the coordinate and compatibility step in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Example
4.2, printed pp.9–10. Let L/K be an extension of number fields and S a
finite set of finite places of K. The coefficient bases are the original
S-integer ring A of K and the integer ring B of L with exceptional set
the full preimage of S. The enlarged lower support T contains S; every
infinite place is always retained. The constructions keep A and B fixed
as T increases. Fields, rings and schemes share an arbitrary universe.

`OriginalPlace` is the disjoint union of the original infinite and finite
places. `OriginalCompletion` is the corresponding actual completed field.
`fieldCoefficient` gives the original field embedding, without introducing
a further algebra instance on this branch-dependent family.
`fieldProjection` evaluates an actual enlarged-level adele at one original
place and regards even an outside-support integer coordinate in its
completed field. It is an A-algebra map. `fieldProduct` collects all these
maps; `fieldProduct_injective` follows by extensionality of the actual
infinite product and finite restricted product.

For any model Y over A that is separated over A and whose underlying
space is quasi-separated, `point_ext` proves that its actual level points
are determined by all original completed-field coordinates. The level
ring is reduced because it injects into a product of fields. The existing
separated-scheme coefficient-injectivity theorem and injectivity of the
actual product point map then detect equality of Y-points. This lemma
uses neither local finite type nor quasi-compactness of Y.

`PlacesAbove`, `upperPlace` and `completionCoefficient` retain actual
upper places and the original lower-to-upper completion embeddings, for
both infinite and finite places. `completionCoefficient_algebraMap`
proves compatibility with the original field coefficients.
`upperFieldCoefficient` first projects a lower level into a lower
completion and then applies the original completion embedding. Its
compatibility theorem retains both original integral bases, using the
existing embedding formulas on elements of K.

`lowerPlace` and `abovePlace` remove the support-dependent branch from a
local factor's index and place-above witness. `upperFactorFieldAlgHom`
is the identity for field factors and the completed valuation-subring
inclusion for outside-support integer factors. The original upper
coefficient formula makes it a B-algebra map.
`factorPointHomeomorph_left` proves that the published regrouping map
preserves the underlying scheme morphism. Its heterogeneous equality
accounts for the two presentations of the same local coefficient ring.
In each of the three branches, the published map is the identity
homeomorphism transported between equal B-algebra structures. The private
transport lemma permits an arbitrary equality proof between the
homeomorphism types; eliminating the algebra equality and then this
proof reduces the underlying-morphism identity to reflexivity.

`localCoefficient` is the literal lower-level factor projection followed
by the original local completion algebra map. Its compatibility theorem
preserves the original A and B coefficients. Composing with the upper
factor-to-field inclusion gives exactly `upperFieldCoefficient`.
For locally finite type Y over B, `localPointMap_fieldEvaluation`
identifies the original completed-tensor local counit, followed into the
upper field, with canonical evaluation on the whole lower level. The
proof uses the generic original-counit evaluation identity and upper
coefficient naturality, together with the existing finite-projective
extension B/A. `fieldEvaluation` packages this actual Y-point.

Assume further that Y is quasi-compact and quasi-separated and has a
specified relative immersion into finite-dimensional projective space
over B. `levelPoint_fieldCoordinate` identifies every upper field
coordinate of the published fixed-model Weil level homeomorphism with
the corresponding local counit followed into its field. It combines the
literal projection law, the regrouping identity and the original local
component law. Spectrum functoriality supplies the integer-to-field
inclusion in the outside-support branch. `levelPoint_fieldEvaluation`
then identifies the coordinate with canonical whole-level evaluation.
`levelPoint_fieldEvaluation_at` uses actual lower and upper places as
indices; its proof chooses an infinite, supported finite or
outside-support finite factor as appropriate.

`upperTransition` is the literal inclusion between upper full-preimage
levels. `upperTransition_pointField` proves that every original upper
field coordinate commutes with it and needs no geometric hypothesis on
Y. `fieldEvaluation_natural` proves that lower support enlargement leaves
canonical upper-field evaluation unchanged; it needs local finite type
of Y and follows from lower coefficient naturality and equality of the
literal evaluated coefficients.

Finally, `levelPoint_natural` proves that the constructed fixed-model
Weil homeomorphisms commute with both literal support inclusions. The
relative projective immersion supplies separatedness over B. Applying
`point_ext` reduces the result to each original upper place. Its
restriction is formed by comapping an infinite place, or by taking the
underlying finite place. The coordinate/evaluation identities at the two
levels and the two coefficient naturality laws finish the proof. Thus
the compatibility belongs to the actual maps and is proved, rather than
assumed as extra data. Full adelic assembly and the generic-fiber/spread
comparison remain separate obligations of the whole-paper task.

The exported abbreviation `OriginalPlace` reuses the existing
`Langlands.Global.NumberFieldPlace` carrier.
