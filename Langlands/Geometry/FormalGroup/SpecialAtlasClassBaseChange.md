# Coefficient extension of special and height-certified atlas classes

Coefficient extension of actual special formal division-order atlases descends
to their formal comparison classes. It also descends within the subtype
carrying actual height d² certificates. Forgetting those height certificates
commutes with the resulting class maps.

## Source and scope

This is derived infrastructure for Drinfeld, *Coverings of p-adic symmetric
regions* (1976), printed p.109 (PDF page 3). The paragraph immediately before
section 2 permits formal groups glued from formal groups over localizations.
Section 2 A defines special formal division-order modules and uses
isomorphism classes of objects with height d² in its functor. Registered
source: `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The present quotient maps are internal consequences of the actual atlas and
comparison constructions, rather than a separately stated source theorem.

The parameters are a nonarchimedean local field K, a finite-dimensional
central division K-algebra D, a supplied K-embedding iota of a field L into
D, and a commutative O_K-algebra R. Each input special atlas supplies its
unramified full-degree integer-subfield certificate and its distinct
geometric tangent-character certificates. Coordinates are `Fin d`, where
d is `CentralSimple.reducedDegree K D`. Principal covers may be infinite.
Coefficient extensions `S : CommAlgCat.{v} R` and coefficient tests have
universe v; complete-family modules have universe v+1. Geometric tangent
tests have universe `max u v`, as in the imported specialness definition.
No flatness or injectivity of R → S is assumed.

These are classes of the supplied actual atlas presentations. This module
does not prove existence of the integer subfield, specialize D to invariant
1/d, or classify arbitrary formal schemes.

## Special-atlas class map

`SpecialAtlas.baseChangeComparison f S` applies coefficient extension to
the supplied actual division-order-linear formal comparison f. The imported
construction extends both principal refinements and composes the inverse
left refinement/base-change isomorphism, the coefficient extension of the
original formal isomorphism, and the right refinement/base-change
isomorphism. It retains actual formal maps, coefficient naturality, overlap
compatibility, commutation with every division-order element, and the two
formal inverse equations. In particular, it handles coincident images of
cover generators by the actual transition maps between selected charts.

`SpecialAtlas.equivalent_baseChange` maps a witness of existence of such a
formal comparison to this constructed witness. Consequently
`SpecialAtlas.IsoClass.baseChange q S` is well defined by `Quotient.map`.
`baseChange_classOf` computes it on any supplied actual special atlas by
reflexivity. The construction uses no chosen representative of q and no
comparison chosen from class equality.

## Height-certified class map and the forgetful square

`HeightSquaredAtlas.baseChange X S` extends X's underlying actual special
atlas and applies `SpecialAtlas.baseChange_height` to X's own certificate.
That certificate includes irreducibility of pi in O_K, nilpotence of its
actual image in R, and actual chart `HasPiHeight pi q (d^2)` certificates,
where q is the cardinality of K's residue field. The imported preservation
theorem maps nilpotence along R → S and maps the scalar-kernel height data
along the actual chart coefficient maps; it retains irreducibility.
`val_baseChange` identifies the underlying atlas by reflexivity.

`HeightSquaredAtlas.equivalent_baseChange` uses the same actual formal
comparison extension on these already certified inputs.
`HeightSquaredAtlas.IsoClass.baseChange` then descends this operation
within the certified subtype, and `baseChange_classOf` computes it by
reflexivity.

`HeightSquaredAtlas.IsoClass.forgetHeight_baseChange` states

    forgetHeight (baseChange q S) = baseChange (forgetHeight q) S.

Quotient induction reduces this square to an actual certified atlas, where
both sides are definitionally its underlying extended special-atlas class.
No height certificate is inferred for an arbitrary equivalent special
atlas, and no height-reflection result is used.

Identity and iterated coefficient-extension comparison laws are separate
obligations. This module supplies class maps and their forgetful square,
not yet a varying-base moduli functor. It supplies no framing object,
rigidifying quasi-isogeny, action on Drinfeld triples, or representability
result.
