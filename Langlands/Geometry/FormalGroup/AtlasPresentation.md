# Classes of formal atlas presentations

`AtlasPresentation.IsoClass` is the quotient of actual finite-dimensional
principal-cover formal O-module atlases by existence of a formal isomorphism
after actual refinements. Equality of classes is exactly existence of such a
comparison. A chosen representative supplies actual full-family and Nilp
point functors, with natural isomorphisms from each presentation in the class
induced by a chosen formal comparison.

## Provenance and scope

This is derived infrastructure for Drinfeld's convention allowing formal
groups obtained by gluing formal groups over localizations: Drinfeld,
*Coverings of p-adic symmetric regions* (1976), printed p.109, paragraph
immediately before section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The bundling, quotient and representative constructions are derived from the
implemented formal atlas comparisons; they are not separately stated
theorems of Drinfeld.

O and R are arbitrary commutative rings, with an O-algebra structure on R.
A presentation specifies a natural number n and an actual
`BasicAtlas O R (Fin n)`. Thus the construction includes arbitrary finite
dimensions in these chosen coordinate types. It does not provide a coordinate
reindexing construction from every other finite type. Principal covers may be
infinite, and chart laws may vary. Tests are R-algebras in R's universe v;
the point modules lie in v+1.

The equivalence relation remembers existence of a formal comparison, not a
chosen map. Different comparison witnesses may be different automorphisms.
Neither equality of their point maps nor canonical maps between representatives
is claimed. The representative and the comparison with it use classical
choice. This module does not construct a category of these classes, change of
base on classes, special formal modules, framing, heights, a moduli functor
or a representing object.

## The relation and quotient

`Equivalent X Y` is the proposition
`Nonempty (BasicAtlas.Comparison X.atlas Y.atlas)`. The imported comparison
contains actual localization containments and a formal atlas isomorphism on
equal finer covers. It is a stronger input than a bare point-functor
isomorphism.

`equivalent_refl` uses the constructed reflexive comparison.
`equivalent_symm` reverses the contained formal comparison.
`equivalent_trans` extracts two comparison witnesses and uses their constructed
product-cover composite. Thus `comparisonSetoid` has all three equivalence
laws from actual formal maps. `IsoClass` is its Lean quotient, and `classOf`
is the quotient map.

`classOf_eq_iff` applies the exact equality criterion for that quotient.
Consequently `classOf_eq_of_comparison` sends any genuine comparison to
equality of classes. `comparisonOfClassEq` uses classical choice in the
reverse direction: equality supplies a genuine comparison, without
specifying which of the possible comparisons is selected.

## Chosen representatives and their actual points

`IsoClass.representative` is `Quotient.out`; `classOf_representative` proves
that it belongs to the original class. `IsoClass.pointFunctor` is precisely
the chosen representative atlas's full-family O-module point functor on
R-algebras. `IsoClass.nilpPointFunctor π` is the same atlas's point functor
restricted to the actual category where the image of π is nilpotent.

For a presentation X, `comparisonToRepresentative` first uses
`classOf_representative` and `classOf_eq_iff` to obtain existence of a
formal comparison from X to the chosen representative of its class.
Classical choice selects that comparison.
`pointFunctorIsoToRepresentative` and
`nilpPointFunctorIsoToRepresentative` are the imported natural isomorphisms
induced by this actual comparison. Their components restrict a full family
to the finer cover, apply the selected formal coordinate isomorphism and
glue the resulting family. Naturality and O-linearity follow from those
constructed maps and their proved inverse laws. No representing object or
arbitrary supplied point equivalence is used.
