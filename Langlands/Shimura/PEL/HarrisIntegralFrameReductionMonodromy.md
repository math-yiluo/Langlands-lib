# Monodromy of the finite reduction of Harris frames

This internal comparison applies the Library's actual full Weil monodromy
and finite Tate monodromy to `HarrisIntegralFrameReduction`. The base,
positive polarized datum, and field-valued point are fixed. The action on
frames uses the published rational Weil geometric transport: it acts on the
Tate target and on the Weil twist together. The right action is the original
precomposition action, with the Harris auxiliary involution unchanged.

`harrisIntegralFrameCondition_monodromy` proves preservation of normalization.
Rationalization intertwines the integral and rational Tate actions. Thus an
integral witness for a vector of the source span can be sent forward by
integral monodromy; a witness for the translated frame can be sent back by
the inverse integral automorphism. `harrisIntegralFrameReduction_monodromy`
uses injectivity of full Tate rationalization to identify the restricted
translated frame with the integral translate on source vectors. Evaluation
at the positive index `m` then intertwines this map with the actual monodromy
on `m`-torsion. Surjectivity of the source quotient map gives the formula on
all of `Λf/mΛf`.

At an algebraically closed field-valued point, with the positive integers
units on the base, an invariant normalized orbit at a subgroup contained in
`K(m)` gives pointwise monodromy-fixed finite torsion values
(`harrisIntegralFrameReduction_fixed_of_le`). Indeed, the left translate is
related to the original frame by a right action from the level subgroup,
so both frames have the same reduction by the principal-congruence orbit
criterion. Conversely at exactly `K(m)`, if all finite torsion values are
fixed, equivariance gives equality of reductions with every translate. The
same criterion identifies these translates with the original right orbit
(`harrisIntegralFrameReduction_fixed_iff`). This converse is not asserted for
a smaller subgroup.

`harrisIntegralFixedTorsion` is the additive subgroup of the actual finite
Tate level fixed by every geometric monodromy element. At a transporter
level `U` whose subgroup lies in `K(m)`, `harrisIntegralLevelReduction`
starts from an element of the existing fixed-orbit tower and its existing
`HarrisIntegralLevelCondition`. It selects a normalized frame representing
that orbit and restricts the codomain of its reduction to the fixed
subgroup. `harrisIntegralLevelReduction_apply` proves the formula using any
normalized representative: any two such representatives differ by the
right level subgroup and therefore have equal reduction by the same
principal-congruence comparison.

This module gives finite values at the chosen point, with their invariance
and independence of the representative at that point. It does not construct
global sections, compare distinct points or base changes, or prove moduli
representability.
