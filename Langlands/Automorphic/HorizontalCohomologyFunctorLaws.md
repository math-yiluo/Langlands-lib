# Identity and composition for actual horizontal cohomology transport

This internal API applies to an arbitrary-universe number field `F`, a positive
natural rank `n`, actual complex `OperatorRealization F n` objects, and every
natural degree `q`, including zero. It uses the existing horizontal cycles and
cohomology quotients, together with their finite adelic representations. The
horizontal cochains retain every-slot vanishing on the compact Lie subalgebra
and equivariance under every element of the full standard infinite compact
group. No new chain-compatibility or nonvanishing hypothesis is added.

`Intertwiner.horizontalCohomologyMap_id_apply` proves that transport by the
identity full operator intertwiner fixes every actual cohomology class.
`horizontalCohomologyMap_id` gives this identity as equality of bundled finite
adelic intertwiners.

For arbitrary composable full intertwiners `A : S.Intertwiner T` and
`B : T.Intertwiner U`, `horizontalCohomologyMap_comp_apply` proves that transport
by `B.comp A` agrees on every cohomology class with first transporting by `A`
and then by `B`. `horizontalCohomologyMap_comp` proves the corresponding
equality of bundled finite adelic intertwiners. Thus these are laws for the
already constructed actual quotient transport, with its original carriers.

The pointwise proofs use `Quotient.inductionOn'` to reduce an arbitrary quotient
class to a closed horizontal representative. Definitional computation of the
existing quotient transport reduces the identity or composition equation to
an equality of classes of transported cycles. Congruence under the quotient
projection reduces this to equality of cycles. Two applications of subtype
extensionality and alternating-map extensionality expose the coefficient
value, where the identity and composition equations are reflexive. For each
bundled law, intertwiner extensionality and linear-map extensionality reduce
the assertion to its pointwise law. All four declarations are typed proof
abbreviations with complete proof terms; none is registered with the simplifier.

The provenance is internal: the existing `HorizontalCohomologyTransport`
constructs these actual quotient maps from full operator intertwiners, and the
generic `HorizontalCohomologyIntertwiner` already supplies their abstract
functor laws. This module proves the actual specialization directly by quotient
induction and coefficient computation. Its twelve named local additive-group
instances are canonical `Submodule.addCommGroup` structures: five function
spaces, three realization spaces, three generic horizontal cochain spaces,
and one cycle-space family. They retain the existing carriers and operations.
The module imports only published construction and class modules.

This pair establishes only identity and composition of actual quotient
transport. It adds no operator-equivalence construction, analytic comparison,
smoothness or topology result, finite-dimensionality or nonvanishing theorem,
and does not complete the broad global definition infrastructure.
