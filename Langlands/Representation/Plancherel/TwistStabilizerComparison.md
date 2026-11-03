# Central restriction and actual unramified twist stabilizers

Author: Worker 200.

This is a derived construction toward J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)* (2003),
source ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
III.7, printed p.273 (PDF p.39), defines the stabilizer of a discrete-series
class inside the full unramified character group and uses it in the unitary
orbit quotient. I.1, printed p.239 (PDF p.5), identifies the unitary character
subgroup and states the finite-kernel split-center restriction. The proof of
III.7.1, printed p.274 (PDF p.40), uses the finite group \(G^1A_G\backslash G\).

Here the quotient, restriction kernel, descent, embedding and stabilizer
comparison are constructed for generic group data, with the finite-quotient
premise displayed. The proof route uses the published general central-character
theorem and elementary finite-group character facts. It does not import the
source's Bernstein-center argument or assume spectral finiteness.

## Data and exact conditional scope

The group universe `uG`, representation-carrier universe `uV`, and index
universe `uI` are independent. Initially \(G\) is a group with a topology,
\(\nu_i:G\to\mathbb R_{\geq0}^{\times}\) is an arbitrary indexed family of
algebraic positive characters, and \(A\) is a subgroup. Write
\[
 N=\operatorname{commonNormKernel}(\nu)=\bigcap_i\ker\nu_i.
\]
The imported `unramifiedCharacters ν` consists of actual continuous
\(\mathbb C^\times\)-valued characters trivial on \(N\).

Descent to \(G/(N\vee A)\) requires `A.Normal`; normality of \(N\) is already
proved in the imported construction. Finiteness and the norm-one conclusions
require exactly
`[Finite (G ⧸ (commonNormKernel ν ⊔ A))]`.
They do not assume finiteness of the stabilizer.

For twisting and stabilizers the group additionally has
`NonarchimedeanGroup G`. This supplies the topological-group laws and the
open-subgroup neighborhood basis used to prove that the actual continuous
characters have open kernels. The subgroup \(A\) must be central, expressed as
`hA : A ≤ Subgroup.center G`.

Only the final discrete-series comparison uses a measurable space on \(G/A\)
and a Haar measure \(\mu\) there. These are precisely the data of the imported
`DiscreteSeriesClass A hA μ`; no measure comparison is proved here. Its ambient
canonical `SmoothDualClass` retains irreducibility and admissibility.

For actual reductive rational points, \(\nu\) must be the published actual
rational norm-character family and \(A\) the actual split central subgroup.
The finite quotient must still be proved for those objects. Neither finite
generation of rational characters alone nor a statement of finite-index
character restriction is used as a substitute for that proof.

## Restriction and quotient character construction

`unramifiedCharacterRestriction` is the multiplicative homomorphism sending
\(\chi\) to its restriction to \(A\), forgetting continuity in the target.
`unramifiedCharacterRestriction_apply` is its actual evaluation formula.
`centralTrivialUnramifiedCharacters` is its kernel as a subgroup of the
unramified character group. `mem_centralTrivialUnramifiedCharacters` proves
that its membership condition is exactly \(\chi(a)=1\) for all \(a\in A\).

`centralTrivialUnramifiedCharacterDescend` takes an element of this kernel
to an algebraic character of the actual quotient \(G/(N\vee A)\).
Triviality on \(N\) comes from unramified membership, and triviality on \(A\)
from the restriction kernel; `sup_le` combines them for `QuotientGroup.lift`.
`centralTrivialUnramifiedCharacterDescend_mk` states that evaluation at the
coset of \(g\) is the original value \(\chi(g)\).
`centralTrivialUnramifiedCharacterDescend_injective` evaluates equal descended
characters at every such coset and uses extensionality through the two
subtypes and the continuous homomorphism.

`finite_centralTrivialUnramifiedCharacters` transfers finiteness along this
injection. Mathlib's finite-character instance for maps from a finite group
to the units of an integral domain supplies finiteness of the quotient dual.
Commutativity of the quotient is not an added assumption.
`centralTrivialUnramifiedCharacter_norm_eq_one` composes a descended character
with the units coercion homomorphism to \(\mathbb C\). Every element of the
finite quotient has finite order, so its image has finite order and complex
norm one. The evaluation formula identifies this image with \(\chi(g)\).

## Central-character bridge and full stabilizer

`smoothDualClass_twist_eq_self_on_center` needs only `IsTopologicalGroup G`,
an actual canonical smooth-dual class \(\omega\), a character with open kernel,
and equality of the twisted class with \(\omega\). It proves \(\chi(z)=1\)
for each central element \(z\). Quotient induction selects an actual
irreducible admissible smooth object. `Quotient.exact` gives its isomorphism
with the twisted object; inversion, the full-subcategory inclusion and
`SmoothRep.equivOfIso` give the correctly oriented representation equivalence.

The proof then reuses the published
`Classification.IntegralTwistFreeness.character_eq_one_on_center` from
`CuspidalIntegralTwistFreenessProof`. That helper is stated for an arbitrary
topological group and representation-carrier universe, despite the GL
application in its containing module. It uses the published admissible Schur
central character, a nonzero vector, the intertwining identity and scalar
cancellation. No GL or characteristic-zero hypothesis enters this bridge.

`unramifiedTwistStabilizer_le_centralTrivial` applies this bridge to the actual
unramified twist action and the inclusion \(A\leq Z(G)\).
`unramifiedTwistStabilizerEmbedding` combines the inclusion with the injective
quotient descent, embedding the full stabilizer into
\(\operatorname{Hom}(G/(N\vee A),\mathbb C^\times)\).
`finite_unramifiedTwistStabilizer` transfers finiteness through that embedding.
`unramifiedTwistStabilizer_norm_eq_one` applies the restriction-kernel norm
formula to every stabilizer element. Both conclusions retain the explicit
finite-quotient premise and hold for every canonical smooth-dual class.

## Comparison with the actual discrete-series orbit stabilizer

For \(\omega:\operatorname{DiscreteSeriesClass}(A,h_A,\mu)\),
`discreteSeriesStabilizerEquivFull` constructs a multiplicative equivalence
\[
 \operatorname{discreteSeriesStabilizer}(\omega)
 \;\simeq\;
 \operatorname{unramifiedTwistStabilizer}(\omega.\mathrm{val}).
\]
The forward map forgets the unitary proof and takes the underlying-class
equality of the fixed discrete-series class. The inverse supplies the proved
norm-one condition and lifts the fixed-class equality through subtype
extensionality. Both maps retain exactly the original continuous character.
Their inverse and multiplication laws follow from subtype extensionality.
`discreteSeriesStabilizerEquivFull_apply` records this identity at every
group element. `finite_discreteSeriesStabilizer` transfers the full
stabilizer's proved finiteness through this equivalence.

Thus, under the displayed premise, the unitary stabilizer in the previously
constructed `discreteSeriesOrbitEquiv` identifies with the full stabilizer
written in III.7. This does not change the orbit action or its representatives.
No finiteness of the set of discrete-series twist orbits, finite spectral
support, smooth orbit manifold, orbit measure, formal degree or Plancherel
identity is asserted. Those and the actual split-center finite-quotient
realization remain separate obligations.
