# Minimal actual parabolics with nonzero unitary Jacquet part

This derived supporting construction supplies the minimal choice used at the
start of Renard, *Représentations des groupes réductifs p-adiques*, 2026,
VII.2.6, first proof paragraph (printed p.231 / PDF p.237).
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard chooses a minimal standard parabolic whose unitary Jacquet part is
nonzero, observing that the whole group has this property. The present
construction chooses among all actual rational parabolics. Its minimality is
inclusion of subgroup functors on every test scheme. It does not assert that
the chosen parabolic is standard or compare it with a chosen standard family.

`UnitaryJacquetSupportData` stores the actual parabolic, its rational Levi,
matching geometric unipotent radical and multiplication isomorphism, an actual
split component of the Levi, and nontriviality of the corresponding actual
unitary Jacquet part. The field and representation carrier have independent
universes. The ambient rational-point topology is the canonical one, with the
local-field, local-compactness and nonarchimedean-group assumptions retained.

`UnitaryJacquetSupportData.IsMinimal` says that any other such datum whose
parabolic subgroup functor lies in the chosen one has the same subgroup
functor. The coordinate-kernel criterion proves this minimality by factoring
the contained closed subgroup through the chosen one. Coordinate ideals
reverse containment, so maximality makes the two ideals equal. The published
affine closed-immersion criterion makes the factor an isomorphism; its inverse
gives the reverse inclusion of subgroup functors.

`UnitaryJacquetSupportData.exists_minimal` applies the ascending chain condition
on ideals of the noetherian affine coordinate ring to obtain a maximal
coordinate kernel among a nonempty family. It assumes that the ambient
structure morphism is locally of finite type, in addition to the ambient
affineness. It needs no classification or finiteness theorem for parabolics.

For a nonzero normalized-exponent tempered representation of a connected
reductive group, `nonempty_unitaryJacquetSupportData` uses the actual identity
parabolic and the previously constructed nonzero unitary identity Jacquet
part. Smoothness of the ambient group supplies local finite type. Thus
`exists_minimal_nontrivial_unitaryJacquetPart` gives the minimal supported
parabolic without an extra finite-type or presentation-existence premise.
`minimalUnitaryJacquetSupport` chooses such a datum, and its companion theorem
proves minimality of that choice.

This unit does not prove unitary Jacquet transitivity, temperedness or square
integrability of an irreducible quotient, an induction embedding, uniqueness,
unitarizability, or any of the three final VII.2.6 statements. The noetherian
coordinate-ideal argument is an internal derived proof of the minimal choice,
rather than the standard-parabolic proof route used in the source.
