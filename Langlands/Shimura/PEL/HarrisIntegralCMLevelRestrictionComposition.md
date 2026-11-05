# Composition of original Harris fixed-level restriction

This is an internal deduction from the actual frame and raw-orbit restriction
maps and the original fixed-level towers. It constructs the fixed-level tower
comparison for equal integral actions and proves composition of the published
`harrisIntegralCMFullActionLevelRestriction`. It introduces no external
literature assertion or geometric existence premise.

The arithmetic carriers, schemes and point field have universe zero and retain
the Harris CM fields, central simple unitary datum, normalized signature charts
and scalar-tower hypotheses of the existing constructions. The actual abelian
family `B`, its dual witness, dual-valued homomorphism, tensor/Picard
prerequisites, finite Weil transition compatibility and rational adelic
comparison are supplied. Every test used is a quasi-separated object of
`Over S`. The torsion finite-etale statement, finite-etale roots of unity,
invertible torsion orders, and finiteness of finite-etale fibres at the points
used to form each fixed-level tower remain explicit. The point field need not
be algebraically closed. There is no connectedness, local noetherianity or
finite-etale hypothesis on the test morphisms.

## Equal actions on one direct family

For two literally equal integral-order actions `a` and `a'` on the same direct
family `B_T`, `harrisIntegralCMWeilFrameActionEq_monodromy` proves that the
constructed actual frame comparison intertwines the original monodromy action
of the same geometric fundamental group. The comparison changes only the
module-linearity proofs and preserves every actual Tate value. On each such
value, monodromy uses the same actual rational geometric transport, so subtype
and linear-equivalence extensionality give the stated equality definitionally.
No monodromy compatibility premise is added.

`harrisIntegralCMFullActionLevelActionEquiv` applies `InvariantOrbit.equiv` to
that frame equivalence, its proved right-equivariance, the identity isomorphism
of the fundamental group, and its proved monodromy compatibility. Its source
and target are precisely the original monodromy-fixed right-orbit levels with
actions `a` and `a'`. The opposite right-action convention and each original
Harris level subgroup are preserved. Fixedness is required of the orbit class;
there is no choice of a fixed representative.

`harrisIntegralCMFullActionLevelActionEquiv_val` states that its underlying raw
class is exactly the existing constructed `harrisIntegralCMWeilRawActionEq`
applied to the input class. This equality is definitional.
`harrisIntegralCMFullActionLevelActionIso` assembles these equivalences into an
isomorphism of the original Harris-indexed towers. For every original level
arrow, subtype extensionality reduces naturality to `RightOrbit.map_translate`
for the actual frame comparison and its proved right-equivariance. The
original transporter element and subgroup-respect condition are used.

## Repeated original restriction

Let `f : T' → T` and `g : T'' → T'` be arbitrary morphisms of the supplied
tests, and let `u` be the point of `T''`. Write

- `aD = (relativeEndRestrict B f).comp a`;
- `aComposite = (relativeEndRestrict B (g ≫ f)).comp a`;
- `aSuccessive = (relativeEndRestrict B g).comp aD`.

The already proved `harrisIntegralCMRestrictionAction_comp` is a literal
equality of the last two integral ring actions. The construction
`harrisIntegralCMFullActionLevelRestrictionCompIso` specializes the fixed-level
action comparison to this equality, in the direction from composite to
successive action. It is an isomorphism of the full original level towers on
the same actual final direct family `B_T''` at `u`.

The theorem `harrisIntegralCMFullActionLevelRestriction_comp` starts with an
original fixed level `r` of `B_T` at `u ≫ (g ≫ f).left`. Restrict it using the
published actual map for `g ≫ f`, then apply the constructed tower comparison.
The result equals first transporting `r` to the point
`(u ≫ g.left) ≫ f.left` by the published `weilAdelicLevelPointEq` for
associativity, then applying the published actual restriction for `f`, followed
by that for `g`. The equality is in the original fixed-level object with the
successively restricted literal action. The finite-fibre witnesses at both
associatively equal base points are supplied explicitly; they impose no
additional geometric condition, and their proof choices are irrelevant.

The proof first projects to underlying raw classes, using the established
value formula for the action comparison. It applies the injective actual raw
evaluation equivalence for `g` and then that for `f`. The proved
`harrisIntegralCMRestrictionRaw_comp` replaces the composite evaluations by
composite restriction followed by the canonical raw point comparison. The
proved `harrisIntegralCMFullActionLevelRestriction_rawValue` cancels each of
the three original fixed-level restrictions against its actual raw evaluation.
Finally `weilAdelicLevelPointEq_val` identifies the underlying raw value of the
fixed-level point comparison. Subtype extensionality concludes the equality.
Thus composition is proved for the original maps, rather than for newly
defined replacement restriction maps.

The contribution concerns restriction of supplied families and their actual
fixed adelic levels. Full-test naturality of the finite-orbit-cover comparison,
disconnected-test gluing, and the full normalized rational-isogeny moduli
comparison remain obligations. It constructs no representing PEL scheme and
proves no new existence, admissibility, smoothness or division-case
projectivity assertion. `DivisionCMRepresentabilityStatement` and all imported
Lean/Markdown pairs are preserved.
