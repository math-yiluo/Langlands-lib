# Finite torsion reduction of normalized Harris frames

This is an internal comparison for the ordinary-moduli route to Harris CM
representability. It uses the published normalized Weil frame predicate
`HarrisIntegralFrameCondition` and the actual Harris source span `Λf` in the
finite-adelic scalar extension of `A`. It also uses the source quotient
`HarrisIntegralSourceMod D C m` and principal congruence subgroup
`harrisIntegralAdeleCongruence D C m` from `HarrisIntegralSourceCongruence`.
No new normalization or action on the rational frames is defined.

## Restriction and evaluation

For a positive polarized action datum `X` and a field-valued point `s` of its
base, `harrisIntegralFrameFull` restricts a normalized frame `eta` to an additive
equivalence from `Λf` to the full integral Tate group at `s`. The normalization
predicate gives, for each vector of `Λf`, a full Tate element whose
rationalization is the image of that vector under `eta`. Injectivity of the
published Tate rationalization gives uniqueness and proves the additive laws.
Injectivity of the frame proves injectivity of the restriction, and applying
the inverse frame to the rationalization of a full Tate element proves
surjectivity by the converse direction of normalization. The theorem
`harrisIntegralFrameFull_toRational` gives the characterizing equation.

For a positive integer `m` in the full Tate index set,
`harrisIntegralFrameReduction` composes that restriction with evaluation at
`m`. The composition kills `mΛf`, since the target `Tate.Level` over `s` is
killed by `m`. The additive quotient lift therefore gives a map from the actual
source quotient `Λf / mΛf` to the actual finite torsion group, with the formula
on representatives given by `harrisIntegralFrameReduction_mkQ`.

If the field of `s` is algebraically closed and all positive integers are
units on the base, `harrisIntegralFrameTorsionEquiv` upgrades the same reduction
to an additive equivalence. The full evaluation kernel theorem identifies zero
`m`-coordinate with multiplication by `m` in the full Tate group. Transport
through the restriction shows that source vectors with the same evaluation are
equal modulo `mΛf`. Surjectivity is the full Tate evaluation surjectivity theorem
at `s`, followed by surjectivity of the restriction.

## The exact principal-congruence orbit

`harrisIntegralFrameReduction_right` gives the pointwise formula for the
reduction of `right eta g` when `g` belongs to the source stabilizer. At a source
quotient representative the formula is evaluation of the restricted frame on
the restricted source operator. Both sides use the same full Tate element by
the definition of precomposition and proof irrelevance for its normalization
witness. The action is the original opposite-group right action; the auxiliary
left involution is the one used by the existing Harris datum.

Under the geometric-point and unit hypotheses above,
`harrisIntegralFrameReduction_eq_iff_rightOrbit` says that two normalized frames
of the **same datum at the same point** have equal reductions if and only if
they are in the same original right orbit for the principal congruence subgroup
at `m`. Any two compatible frames differ by a source similitude, by
`FormIso.exists_precomp_eq`. Normalization of both frames forces that similitude
to preserve `Λf` in both directions. The right-action formula and injectivity
of reduction identify equality of reductions with identity of its operator on
`Λf / mΛf`. That identity is exactly the kernel condition defining the
principal congruence subgroup in the stabilizer.

This compares frames and their principal-congruence orbits at a fixed point.
It does not characterize finer level orbits by reduction at `m`, construct
invariant global torsion sections, or construct a moduli scheme.
