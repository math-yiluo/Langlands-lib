# Prescribed-level generation from actual compact-picture expansions

This internal construction turns the published regular compact-picture
generation theorem into generation of the actual induced representation
by its fixed vectors at the same specified level.

Fix an actual semidirect decomposition `P = M ⋉ U`, with `U` and `P` closed,
in a nonarchimedean locally compact group. Assume inner conjugation on `U`
has trivial Haar modulus, so full-parabolic normalization agrees with the
published Levi normalization. Let `K` be compact open with `G = P K`, and
let `L ≤ K` be a specified open subgroup.

The forward map of the published `compactFixedEquiv` from
`Langlands.Representation.Plancherel.CompactIntertwiningCompression`
extends a compact-picture vector fixed by
`L ∩ K` to an actual `L`-fixed vector of normalized Levi induction, at any
unramified parameter. Restriction intertwines the actual `K` actions, and
`L ≤ K` identifies this fixed condition with the specified ambient one.

If the regular translate span of these compact-picture fixed vectors is
the whole compact picture, specialization of its finite expansion at any
one parameter expresses every induced vector as a finite linear
combination of translates of actual `L`-fixed vectors. Every invariant
submodule containing the fixed space therefore contains the entire
representation. This proves `fixedVectorGenerated` at `L`, with no change
of level. The actual equivariant normalization comparison transports this
conclusion to full-parabolic normalized induction of the twist.
The trivial parameter and the actual twist-by-one isomorphism give the
untwisted conclusion.

The final theorem obtains the top regular span from the published
`regularTranslateSpan_eq_top`, with the norm-character index set empty.
It retains exactly the structural inputs of that theorem: a compact
specified level `L`, its Iwahori contraction, its factorization in the
order `U M Ubar`, triviality of `P ∩ Ubar`, normalization of `Ubar` by
`M`, a cofinal compact open factorized basis, and coefficient orbit
generators fixed by the projected `P ∩ L` action. The field of coefficients
is complex and the group and vector universes are independent.

The provenance is this internal specialization and transport of the actual
published compact-picture constructions. No admissibility, finite length,
irreducibility or cuspidality is assumed. The theorem proves generation
under its stated structural and coefficient inputs; it does not claim
that these inputs have been discharged for the host standard family or
that the host fixed-vector category theorem is proved.
