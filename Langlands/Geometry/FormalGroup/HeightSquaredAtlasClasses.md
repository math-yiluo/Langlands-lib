# Classes with actual height-d-squared atlas certificates

`SpecialAtlas.HeightSquaredAtlas.IsoClass pi` quotients the subtype of
actual special atlases that already carry `HasHeightSquared pi`
certificates. Its relation is actual division-order-linear formal
comparison after principal refinement. Every chosen representative
retains its own height certificate.

## Source and hypotheses

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), section 2 A, fixes a special framing module of dimension d
and height d² and requires height d² of the special module in each
triple. The paragraph immediately before section 2 permits formal
groups glued over localizations. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This quotient is internal presentation infrastructure for the
height-certified objects that a later triples construction will use;
it is not an assertion of Drinfeld's full functor or theorem.

The parameters and universe conventions are those of `SpecialAtlas`:
a nonarchimedean local field K, a finite-dimensional central division
K-algebra D, an embedded field L with supplied unramified full-degree
integer-subfield certificate, and a commutative O_K-algebra R.
Coordinates are `Fin d` for `d = CentralSimple.reducedDegree K D`.
Principal covers may be infinite. Coefficient tests have universe v and
complete-family modules v+1; geometric tangent tests have universe
`max u v`. No subfield-existence or invariant-1/d specialization result
is supplied here.

The existing `HasHeightSquared pi` requires irreducibility of pi,
nilpotence of its actual image in R, and actual
`HasPiHeight pi (Nat.card` of K's residue field`) (d^2)` on every original
chart. This includes the actual scalar-kernel projective algebras and
their stalk ranks. Both inputs of the relation already have these
certificates.

## Restricted formal comparison relation

`Equivalent` applies `SpecialAtlas.Equivalent` to the two underlying
certified atlases. Its reflexivity, symmetry and transitivity follow
from the actual formal comparison constructors. `comparisonSetoid`
and `IsoClass pi` form the quotient; `classOf_eq_iff` gives its equality
criterion. `classOf_eq_of_comparison` applies the criterion to supplied
actual formal maps.

`IsoClass.forgetHeight` maps to the underlying special-atlas class.
`forgetHeight_injective` follows because the relation between any two
certified inputs is exactly the relation between their underlying
special atlases: quotient induction reduces the assertion to their two
equality criteria. This argument constructs no new height certificate.

## Refinement and chosen certified representatives

`refine X q` restricts X's actual atlas, action and special certificates,
and uses `SpecialAtlas.refine_height` to map each original chart height
certificate along the localization coefficient map. The same global
nilpotence and irreducibility conditions remain. The actual formal
`comparisonOfRefinement` proves `classOf_refine`.

`IsoClass.representative` uses `Quotient.out` inside the certified
subtype. `classOf_representative` identifies its class.
`representative_height` exposes this representative's own certificate;
`base_nilpotent` exposes its global nilpotence component. The class's
`pointFunctor` evaluates that chosen representative's actual
division-order-compatible families. `nilpPointFunctor` restricts it to
tests where the actual image of pi is nilpotent.

`comparisonToRepresentative` chooses actual formal comparison data
using the quotient equality criterion. Its realized algebra and Nilp
natural isomorphisms are `pointFunctorIsoToRepresentative` and
`nilpPointFunctorIsoToRepresentative`. `comparisonOfClassEq` makes the
same kind of explicit choice from equality of two certified classes.
These choices can yield different automorphisms; they specify no
canonical point map.

No reflection of chart height along arbitrary refinements is used or
proved. In particular, this construction does not infer height for an
arbitrary equivalent special atlas or for the separate chosen
representative of `forgetHeight q`. It supplies no framing object,
triples, varying-base moduli functor or representability result.
