# Maximal tori in a relative Levi subgroup

This internal derived module uses the actual Levi retraction and the published
closed-torus result for homomorphisms with unipotent kernel.
It neither asserts the existence of a torus in a Levi nor proves relative
Levi conjugacy.

Over a field, `IsMaximalTorus.comp_of_radical_complement` assumes an affine
ambient group, a closed complement to a represented unipotent radical, an
actual Levi multiplication isomorphism, and that the complement is locally
of finite type. It proves that a maximal torus of the complement is maximal
in the ambient group. The kernel of the Levi retraction is precisely the
radical on every test scheme. Consequently every proposed larger closed
torus in the ambient group embeds as a closed torus in the complement
through that retraction. The retraction fixes the complement, so maximality
there makes the original comparison map an isomorphism.

Over an arbitrary scheme, `IsFibrewiseMaximalTorus.comp_relativeLevi`
assumes an affine ambient group, a relative Levi embedding `l : L ⟶ P`,
and a globally closed map `t : T.toGrp ⟶ L` from a commutative group scheme which is maximal on
every residue fibre of `L`. It proves that `t ≫ l` is maximal on every
residue fibre of `P`. There is no reductivity or connectedness premise
on `P` in this assertion. The relative Levi predicate supplies smoothness
and closedness of `L`, and a relative radical with an actual multiplication
isomorphism. Affineness of `L` follows from its closed embedding in `P`.
Maximality of `t` at each chosen geometric point follows from the
published field-point maximality theorem. Base change preserves the
multiplication isomorphism, and the relative radical predicate supplies
the full radical on that geometric fibre. The field result above gives
ambient maximality there. The successive-pullback comparison and
field-extension reflection of maximality give maximality on the original
residue fibre. The global closedness assumption on `t` supplies the
closedness needed for reflection.

`RelativeLevi.ambientMaximalTorus` retains the actual composite `t ≫ l`
together with its global closedness, fibrewise maximality, and containment
of its image in the image of `l` on every test scheme.
`RelativeLevi.ambientMaximalTorus_val` identifies the retained map with
that composite. The construction requires the same hypotheses as the
relative lemma; it makes no choice of a new representative.

The provenance is internal: `Rational.LeviRetraction` constructs the
retraction and identifies its all-test kernel, while
`Torus.UnipotentQuotientClosed` and `UnipotentClosedSubgroupProof` provide
the closed-torus assertion with its structural premise discharged.
`Torus.FieldPointMaximality`, `Torus.MaximalBaseChangeReflection`, and
the actual multiplication base-change helper provide the relative
passage through geometric fibres. None of these inputs assumes the
relative Levi conjugacy conclusion.
