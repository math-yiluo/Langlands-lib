# The canonical smooth integral model of the multiplicative group

This internal construction uses the published actual multiplicative group,
its base change isomorphism, smoothness, and integral-model definitions.
All rings, fields and schemes use an arbitrary common universe `u`.

`isAffineHom_gm` proves affineness of the actual multiplicative group over
every scheme. Its structural morphism is the pullback of the affine map
from the spectrum of the integral Laurent polynomial ring to the spectrum
of `ULift ℤ`. Affine morphisms are preserved by base change.

For a commutative domain `R` with supplied fraction field `K`,
`IntegralModel.multiplicative R K` has integral group exactly `Gm (Spec R)`.
Its generic isomorphism is the published `Gm.baseChangeIso` for the actual
map `Spec K → Spec R`. The published `smooth_gm` supplies smoothness,
flatness and local finite type. Affineness is the preceding theorem.
No Noetherian or number-field hypothesis is required.

`multiplicativeSectionsEquiv` identifies its integral sections with `Rˣ`
using the published affine point equivalence. The theorem
`multiplicative_integralPointMap` proves that generic evaluation corresponds
under this equivalence to `Units.map (algebraMap R K)`. The proof applies
the unit-preserving property of `Gm.baseChangeIso`, cancels the pullback
point equivalence defining `baseChangeSectionHom`, and uses naturality of
the unit-valued point equivalence and the spectrum global-section isomorphism
under the actual ring map.

The module supplies a smooth source model for subsequent cocharacter
descent. It does not descend a supplied cocharacter, construct a reductive
ambient model, or prove the simultaneous reductive/parabolic spreading
existence statement.
