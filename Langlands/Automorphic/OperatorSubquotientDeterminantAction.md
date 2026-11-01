# Actual finite-order character action on automorphic quotient classes

Author: Worker 2. This internal construction completes the character identity
and product laws for the actual `OperatorSubquotient` determinant transport.
The number field has arbitrary universe, the rank is any natural number and
coefficients are complex. The two characters have explicit finite-order proofs.
No CM-field hypothesis is imposed. The imported finite-order subgroup and the
previously constructed quotient classes retain their existing meanings.

Write `Mχ` for the actual finite-smooth determinant multiplier, `Cχ` for the
actual automorphic operator-algebra conjugation and `Dχ` for the induced
quotient linear equivalence. Extensionality through the nested function
subspaces proves `M1(f) = f` and `M(χψ)(f) = Mψ(Mχ(f))`: the latter is just
commutativity and associativity of the complex character values multiplying
the same function. These identities hold on the actual finite-smooth
functions, before taking any module quotient.

The concrete operator conjugation is `Cχ(a) = Mχ⁻¹ ∘ a ∘ Mχ`.
Operator extensionality, injectivity of the actual multiplier and cancellation
of its inverse prove `C1(a) = a` and
`C(χψ)(a) = Cχ(Cψ(a))` for every operator in the automorphic operator algebra.
The order agrees with the actual successive multiplier formula.

`OperatorSubquotient.determinantTwistOneEquiv` is a genuine whole-action
representation equivalence from `Q` to its unit-character quotient image.
Its underlying linear equivalence is exactly `D1`. The existing quotient
covariance and the proved identity conjugation law supply its intertwining
identity.

`determinantTwistMulEquiv` is a genuine whole-action equivalence from the
quotient image for `χψ` to the quotient obtained by twisting first by `χ`
and then by `ψ`. Its underlying map is exactly
`Dψ ∘ Dχ ∘ D(χψ)⁻¹`, with `Dψ` taken on the first twisted quotient.
An abstract composition calculation combines the two existing covariance
identities, and the concrete product conjugation law makes their composite
parameter change equal to the one for `χψ`. If two actual linear equivalences
from the same representation have covariance for that same parameter change,
their composite through the inverse of the first intertwines the target
actions. This proves the construction's whole-action obligation. The exact
application formula holds on every vector of the product quotient; on
`D(χψ)(f)` it reduces to `Dψ(Dχ(f))` by inverse cancellation.
The construction compares the dependent quotient presentations by actual
maps.

Quotient induction and these genuine whole-action equivalences prove
`IsoClass.determinantTwist_one` and `IsoClass.determinantTwist_mul` for the
existing whole-action classes. The product law says that twisting by `χ`
and then by `ψ` equals twisting by `χψ` on classes.
`IsoClass.finiteOrderCharacterMulAction` uses the same constructed class
transport as its scalar operation. The identity law is the one just proved;
commutativity of the finite-order Hecke-character subgroup reconciles the
successive-twist order with the standard left-action multiplication law.
`finiteOrderCharacter_smul` records the exact scalar-operation formula.

Provenance is internal: actual finite-smooth determinant multipliers from
`SmoothDeterminantMultiplier`, their concrete conjugation from
`DeterminantOperatorConjugation`, the actual quotient maps and covariance in
`OperatorSubquotientDeterminantTwist`, the whole-action class descent in
`OperatorSubquotientDeterminantTwistClasses`, and Mathlib's genuine linear and
representation equivalences. `OperatorDeterminantTwistClasses` supplies the
existing finite-order subgroup and the analogous left-action convention for
embedded realizations. The present construction applies to module-quotient
classes. No new original-literature identification is claimed.

The construction adds no quotient evaluation or topology, continuity premise
on arbitrary maps, local tensor-factor selection, quotient cusp or
central-character predicate, or nonzero, irreducible or spectral existence
assertion.
