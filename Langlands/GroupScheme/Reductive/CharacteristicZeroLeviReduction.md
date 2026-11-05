# Reductive quotients and the remaining section input for Levi decomposition

`ReductiveUnipotentQuotient G` records an actual group scheme `Q` over the
same field and a homomorphism `q : G ⟶ Q`. Its fields give connected
reductivity of `Q`, the represented fppf quotient property for the full
scheme-theoretic kernel, smoothness of `q`, and smoothness, connectedness
and unipotence of the actual group scheme `GroupScheme.kernel q`.
It includes no section.

For every perfect field `k : Type u` and smooth connected affine group
scheme `G` over `Spec k`, `nonempty_of_perfectField` constructs such data.
`ofPerfectField` chooses it. Neither construction assumes a radical,
quotient, splitness, reductivity of the source, or an algebraically closed
field.

The construction applies the published `unipotentRadicalExistence` to obtain
a represented ground-field radical `i : U ⟶ G`. The published
`unipotentRadicalQuotient` gives its actual represented fppf quotient
`q : G ⟶ Q` and proves pseudo-reductivity of `Q`.
`perfectFieldPseudoReductive` converts this to connected reductivity under
the field's perfectness hypothesis.

The radical inclusion is closed, hence monomorphic. The quotient predicate
identifies its range with that of the actual kernel on every relative
scheme test. `KernelRepresentative` therefore identifies the actual kernel
with `U` and transfers its smoothness, connectedness and coefficient
representation unipotence. Quasi-compactness of `q` follows from affineness
of the source; the represented smooth-kernel theorem then proves
smoothness of the quotient projection. Rewriting the range equality
expresses its fppf quotient property using the actual kernel inclusion.
These comparisons use all tests, including nonreduced schemes.

`characteristicZeroLeviDecomposition_of_reductiveExtensionSections` is a
conditional reduction to the exact published
`CharacteristicZeroLeviDecompositionStatement.{u}`. Its explicit input says
that over every characteristic-zero field at universe `u`, every smooth
surjective group-scheme homomorphism from a smooth connected affine group
onto a connected reductive group has a homomorphic section when its actual
kernel is connected and unipotent. It assumes neither splitness of the
field nor splitness of the reductive quotient.

For the target's field, characteristic zero supplies perfectness. Apply
the quotient construction to the given `G`, then apply the section input
to its projection. The resulting quotient and section are the target's
`L`, `p` and `j`; the three kernel properties are fields of the constructed
data. All target quantifiers and hypotheses are preserved.

The provenance is internal composition of the five imported Library
interfaces and Mathlib's characteristic-zero perfect-field instance.
Milne, *Algebraic Groups* (2017), Proposition 19.11(b), printed p. 400
(PDF p. 416), describes the perfect-field reductive quotient, and
25.48–25.49, printed p. 559 (PDF p. 575), explains its relation to Levi
subgroups. Those source assertions are represented here through the
published inputs. This module does not prove the remaining Mostow
section-existence input, conjugacy of Levi subgroups, or an unconditional
Levi decomposition.
