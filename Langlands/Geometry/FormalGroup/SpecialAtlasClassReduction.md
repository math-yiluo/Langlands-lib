# Quotient reduction on actual special-atlas comparison classes

This module descends the actual special-atlas reduction through
refined formal comparison. It uses `SpecialAtlasReduction`,
`SpecialAtlasClassBaseChangeAlong` and the actual canonical quotient-square
comparison from `AtlasOrderReductionBaseChange`. It makes no additional
original-literature assertion.

The parameters and universe conventions are those of
`SpecialAtlasReduction`: K is a nonarchimedean local field, D is a
finite-dimensional central division K-algebra, and each actual special
atlas supplies its embedded unramified full-degree subfield and geometric
tangent-character certificates. Coordinates are `Fin d` for the reduced
degree d of D. R is a commutative O_K-algebra, r is any element of R,
and A and B belong to `Nilp R r`. A, B, their principal-ideal quotients
and their tests have the same universe w. Covers may be infinite and
complete compatible families have universe w+1. The quotient A/(r)
need not be reduced or a residue field, and coefficient maps need not
be injective or flat.

`reductionComparison` extends the specified actual `Comparison X Y`
along the quotient map. A comparison stores two principal refinements,
an equality of their covers, and an actual full-order formal isomorphism
between the refined atlases with both inverse equations. The imported
extension construction retains these formal data. The forward and
inverse family equations say that this specified extended comparison
commutes with the quotient-extension equivalences on entire compatible
families. Different comparison witnesses are not identified.

`equivalent_reduction` preserves existence of actual comparison.
`IsoClass.reduction` is exactly the existing quotient-class extension
along `Nilp.quotientO O_K A`; its representative formula is
`reduction_classOf`. The map chooses no representative or formal
comparison.

For an actual morphism `f : A → B` in Nilp, the equation
`Nilp.quotientO_natural O_K f` gives the commuting square of actual
O_K-algebra maps. `reductionBaseChangeIso X f` is exactly the full-order
formal isomorphism constructed for that square. Its source is X
extended to B and then reduced; its target is X reduced and then
extended along the induced A/(r) → B/(r) map.
`reductionBaseChangeComparison` places this same actual isomorphism on
reflexive refinements, retargeting the right refinement by the proved
cover equality. Restriction retains both formal inverse maps and
equations. This constructs the witness for
`classOf_reduction_baseChangeAlong`. Quotient induction then proves
`IsoClass.reduction_baseChangeAlong` for every special-atlas class.
Thus naturality on classes is justified by an actual formal comparison.

`HeightSquaredAtlas.reduction` extends the original actual atlas
together with its own certificates by the same quotient map.
The predicate includes irreducibility of pi in O_K, nilpotence of its
actual image in A, and actual scalar-kernel heights d² on every chart,
with K's residue-field cardinality as q. Pi need not correspond to r.
`val_reduction` identifies the underlying special atlas. The reduced
height-certified inputs compare by the same formal comparison, and
their two routes around the quotient square each retain their own
certificates. No height transfer to an uncertified representative is
assumed.

`HeightSquaredAtlas.IsoClass.reduction` is quotient extension within
this certified subtype. Its representative formula, compatibility with
forgetting height, and naturality under f follow from the constructed
operations and quotient induction. In particular, the height-class
naturality uses the same underlying actual quotient-square comparison.

These operations concern unframed special-atlas classes. They do not
construct a fixed framing module, Drinfeld triples, polarizations,
levels or a representing formal scheme. Invariant 1/d, existence
of the embedded subfield, further square coherence and independence
from arbitrary choices of formal comparisons are not asserted.
