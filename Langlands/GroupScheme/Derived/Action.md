# Automorphic actions on full derived subgroups

Over any field of universe `u`, an actual action of an affine group scheme
by automorphisms on another affine group scheme preserves every supplied
closed representative of the full scheme-theoretic derived subgroup.
`IsDerivedSubgroup.action` constructs the induced actual automorphic action,
and `action_act_comp` states that the inclusion intertwines the two actions
on every test scheme.

The companion theorem `IsDerivedSubgroup.isNormal_comp` applies this action
to ambient conjugation. If the affine ambient group contains the given
affine group as a closed normal subgroup, its full derived representative
is normal in that ambient group after composing the two inclusions.

This is internal support for the arbitrary-field normal-complement task.
The argument combines functoriality of the full derived subgroup with its
published equality under affine base change from a field. Base change along
the structure map of the affine universal action domain `H × D`. The
universal acting point becomes a section over this new base, hence an actual
group-scheme automorphism. Functoriality puts the image of the universal
derived point in the derived subgroup after base change. The base-change
equality transports this membership back to the original field. Restriction
along any pair of test points gives the required stability on every test
scheme. The existing represented-subgroup action construction then gives
the actual induced action and its inclusion identity.

No smoothness, connectedness, perfectness, algebraic closedness or reducedness
assumption is used. The closed derived representative is supplied as an
input; this result does not assert its existence and does not construct a
normal semisimple complement.
