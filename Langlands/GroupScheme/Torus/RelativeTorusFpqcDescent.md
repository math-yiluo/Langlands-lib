# Fpqc reflection of the relative torus property

A group scheme is a relative torus if and only if it becomes a relative
torus after a flat, surjective, quasi-compact base change. The predicate is
the Library's étale-local splitting into finite split tori.

The proof descends the affine and smooth structure morphism along the given
base change. For each point of the original base, choose a point over it.
The comparison of actual residue fibres identifies the fibre over that point
with a scalar extension of the original residue fibre. The field torus
predicate descends along this extension. In particular, all the residue
fibres of the original group are connected. The Library's torus fibre
spreading theorem now gives a Zariski open neighbourhood of each point where
the original group is a relative torus. The relative torus predicate is local
on that open cover. Preservation in the other direction is ordinary base
change of an étale splitting cover.

This is an internal consequence of the Library's fpqc morphism-property
descent, field torus comparison and torus fibre spreading. It supplies
reflection of the torus condition in closed-subgroup descent for the proof
`smoothAffineFiberTorusSubgroupRepresentability` of
`SmoothAffineFiberTorusSubgroupRepresentabilityStatement` (smooth torus-subgroup
representability for groups with affine residue fibres).
