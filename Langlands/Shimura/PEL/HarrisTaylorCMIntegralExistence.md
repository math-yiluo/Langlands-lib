# Integral representatives of every normalized Harris CM class

This is an internal construction from the existing normalized Harris CM
classes, integral class image, polarized integral order model, and level
transport interfaces. It introduces no new assertion from external literature.
It retains the actual universe-zero number fields, central simple unitary
algebra, Harris signature charts, positive auxiliary involution, and original
conjugated reflex scalar map.

The inputs include `Prerequisites` `P`, the full generic
`ProperFibreAmpleAffineOpenStatement`, the named torsion, Weil and adelic
premises, an existing `AdmissibleCMBaseCategory` object `Z`, and a specified
field-valued point with finite cover fibres. The geometric premise remains an
explicit argument throughout the existence results and equivalences. The
construction does not assert that an arbitrary base is admissible.

`cmIntegralRepresentative` takes an actual `HarrisLevelData` representative at
any original Harris level and a proof of the existing joint
`HarrisTaylorCMDeterminantDimensionCondition`. It uses
`cmPolarizedOrderModel` on its polarized action and transports the actual
adelic invariant level orbit by `PolarizedWeilLevel.levelIso`. The transport
uses exactly `cmPolarizedOrderModelIso`, the positive rational unit with
value the prescribed square, and `cmPolarizedOrderModel_multiple`. The new
representative carries the actual integral action restriction on the same
constructed abelian scheme. Its determinant and relative dimension follow
from `cmPolarizedOrderModel_condition_iff`.

`cmIntegralRepresentativeClass_eq` proves equality with the original normalized
class, using `HarrisNumericalWeilLevel.classOf_eq_iff`. Its witnesses are that
same rational unit, rational isomorphism and polarization multiple. The level
equality is definitional because the new orbit was transported by those exact
witnesses. This retains the original rational-isogeny quotient relation.

`integralCMClassCondition_all` first obtains an original representative from
`HarrisNumericalWeilLevel.classOf_surjective`. The published
`determinantDimensionCondition_iff` combines its determinant and numerical
conditions into the existing joint condition. The constructed representative
and preceding class equality then show that the class lies in the exact
integral image.

`integralCMForget_surjective` takes the integral quotient class of this
representative. Combined with the existing `integralCMForget_injective`, it
defines `integralCMClassEquiv`. The forward function is precisely the original
`integralCMForget`, as recorded by `integralCMClassEquiv_apply`.
`integralCMClassTowerIso` assembles these equivalences for the full original
transporter level category. Naturality follows from the existing
`integralCMForget_classMap`; no choice of the inverse function needs to
commute definitionally with level arrows.

These results apply to every original level, without a smallness or division
assumption. They construct integral representatives on existing admissible
test bases. They do not construct a representing scheme, prove smoothness or
division-case projectivity, or establish the main
`DivisionCMRepresentabilityStatement`. Naturality over changes of the test
base and independence of the field-valued point are separate consumer steps.
