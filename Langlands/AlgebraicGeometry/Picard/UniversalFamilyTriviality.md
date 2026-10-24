# Triviality through an actual universal family

This internal categorical assembly assumes a specified actual universal
rigidified line bundle `L` on a parameter scheme `P`, with the published
`IsUniversal` property. It supplies neither the existence of that family
nor a geometric rigidity theorem.

`relativeTrivial` is the canonically rigidified trivial line bundle on the
relative space. `classesPullback_trivial` follows from the published actual
rigidified trivial-pullback isomorphism.

`classifyFamily` uses the inverse of the published classification equivalence
to assign a parameter morphism to an actual family. Its specification,
pullback compatibility and invariance under rigidified isomorphism follow
from bijectivity, pullback coherence, and equality of quotient classes.
`trivialParameter` is the morphism from the base classifying the trivial
family. `classifyFamily_trivial` proves that its pullback classifies the
trivial family on every test scheme.

`isoOfClassifyFamilyEq` recovers an actual rigidified isomorphism from equality
of the classifying morphisms. It uses injectivity of the inverse
classification equivalence, effectiveness of the isomorphism-class quotient,
and choice of an isomorphism from the resulting nonempty type.

`trivialIsoOfTwoRestrictions` takes two maps `a : A ⟶ T` and `b : B ⟶ T`,
an actual family `M` on `T ×_S X`, and actual rigidified trivializations
of its pullbacks along those two maps. It also explicitly assumes rigidity
of morphisms `T ⟶ P` that restrict to the constant trivial parameter along
both maps. It constructs an actual rigidified isomorphism from `M` to the
trivial family.

Classification and its pullback compatibility identify the two restrictions of the classifying map
with the constant trivial parameter. The supplied rigidity hypothesis
makes that parameter map constant on `T`. The trivial-family classification
law and `isoOfClassifyFamilyEq` recover the actual rigidified isomorphism.

No field or geometric property is needed for this categorical assembly.
For the geometric cube application, the independent general Picard
representability and two-axis rigidity proofs must discharge its two
substantial hypotheses. Product and face comparisons must also transport
the cube's actual bundles and trivializations to this relative-family
formulation, and ordinary trivializations must be adjusted to respect
rigidifications. The separate rigidification adjustment construction serves
that purpose. This file alone does not prove the geometric cube theorem.
