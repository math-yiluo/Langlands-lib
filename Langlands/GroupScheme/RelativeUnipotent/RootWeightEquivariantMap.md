# Actual equivariant maps of positive root-weight filtrations

This derived module constructs actual termwise maps from actual equivariant maps
between the represented positive groups. The commutative base ring is arbitrary.
The source and target may have different tori, root data, chart groups, root
families, and dimensions; those data are supplied separately.

`toPositive` is the actual inclusion of every represented term into the
represented term zero. Its construction uses antitonicity of the generated
weight subgroups and factorization through a represented subgroup. Its composite
with the original positive inclusion is the original term inclusion.

The main input is an actual group-scheme map f from the source positive group to
the target positive group. On every coefficient algebra it must intertwine the
two rank-one actions obtained from their supplied realizing cocharacters. The
same positive natural q is required to realize q times the original secondary
weights on both charts. These are action and root-pairing assumptions; no
termwise maps, term membership preservation, or term equality are assumed.

`map_mem_positiveTerm` proves preservation of every original filtration term
inside the positive groups on EVERY scheme test. It rewrites the two original
terms as intrinsic cyclic cutoffs at q*(d+1), applies actual affine-group
intrinsic-weight functoriality, and rewrites back. The tests may be nonaffine,
nonreduced or disconnected. The original unscaled weights and level d remain
unchanged.

`equivariantTermMap` then constructs the actual homomorphism from source term d
to target term d by represented-subgroup factorization. Its companion theorem
proves that following it by the target inclusion equals following the source
positive inclusion by f and the target positive inclusion.

The module requires the actual equivariant positive-group map and common
realizing scale described above. It does not construct geometric conjugators or
prove compatibility of canonical face-cocharacter actions for different tori.
Those inputs, parabolic normalization and effective descent remain obligations
of Task 7200.
