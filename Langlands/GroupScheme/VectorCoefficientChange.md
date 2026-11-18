# Vector quotient coefficient change

This internal adapter for Task 7200 defines actual multiplicative-group
actions and standard vector quotient maps after coefficient change. The
base schemes and commutative coefficient rings are arbitrary at universe
`u`. No field, reducedness, nontrivial-ring or positive-rank assumption
occurs.

`AutomorphicAction.coefficientChange a b` pulls back an actual action of
`Gm` along a base map `b` and restricts its source along the inverse of
the actual `Gm.baseChangeIso`. Thus its acting group is the standard
multiplicative group on the new base. `coefficientChange_act` proves its
pointwise compatibility with the original action under the actual
pullback point equivalence, on every test scheme.

`VectorGroup.charValue_power_eq` identifies the character value of
`Gm.powerHom N` with the `N`th power of the actual underlying global unit.
`matrixHom_isEquivariant_power` uses the actual vector coordinate formulas
and matrix multiplication to prove that every base-ring matrix morphism
commutes with each common natural scalar power.
`isEquivariant_power_of_hasScalarWeight` first applies the existing
positive-weight rigidity theorem to identify the original morphism with
its matrix morphism. It therefore proves equivariance for every common
natural power of that same original actual morphism.

`baseChangeIso_isEquivariant_power` proves that the canonical actual
vector-group base-change isomorphism intertwines the coefficient-changed
power action with the standard power action over the new ring. Its proof
uses preservation of global vector coordinates by `baseChangeIso`,
preservation of global units by `Gm.baseChangeIso`, and the preceding
power-character calculation. It applies to arbitrary scheme tests.

For a coefficient map `ρ : R ⟶ A` and actual quotient
`q : U ⟶ VectorGroup.groupScheme R n`,
`FppfQuotientComparison.coefficientQuotient` is the actual pulled-back map
followed by the canonical vector-group base-change isomorphism.
`isFppfQuotient_coefficientQuotient` preserves the full fppf quotient:
flatness, surjectivity, local finite presentation and equality of the
actual kernel range with the base-changed subgroup functor all follow
from the existing quotient base-change theorem and postcomposition with
an actual isomorphism.

`coefficientQuotient_isEquivariant` proves actual scalar equivariance of
this quotient from the original quotient equivariance. First it compares
the pullback points of the original quotient and action using the
pullback point equivalence; then the vector base-change action comparison
gives the standard scalar action on the target. A consumer supplies the
original actual action and its quotient equivariance, with no additional
base-change equivariance premise.

The provenance is internal: actual action and vector-group base change,
global-unit and coordinate comparisons, the existing full quotient
transport and positive scalar-weight rigidity. Fresh root-chart
comparisons and étale reflection of transition linearity remain separate
consumer obligations.
