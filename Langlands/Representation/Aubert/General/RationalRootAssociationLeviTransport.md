# Actual Levi transport from root association

This internal adapter constructs the actual Levi equivalence and descendant
index comparisons supplied by a given `rootAssociation` witness. It retains
one specified ambient representative throughout. It is a focused prerequisite
for cuspidal-support association; it does not prove that association witnesses
or representation isomorphisms exist.

The field has arbitrary universe `u`. The data are a commutative group scheme
`T`, an affine group scheme `G` over `Spec k`, a monomorphism
`i : T.toGrp ⟶ G`, a cocharacter `ν`, and the point-normalizer and
point-centralizer comparisons `hN` and `hZ`. Labels are the actual simple roots
`SimpleRoot i ν`. Two finite subsets `I` and `J` are associated by an ambient
rational point `n` in the exact published sense: `n` normalizes the torus and
its character action carries `rootSet I` onto `rootSet J`. No global finite
root-system or Weyl-group instance is required here.

`rootAssociation_character_image` reads that equality as the character action
of the scheme normalizer lift supplied by `normalizerEquiv`. The lift has the
same underlying ambient point `n`; this is the published comparison
`weylCharacterAction_point_mk` applied to the normalizer witness already in
`rootAssociation`.

Assume in addition that `G` is connected reductive, `i` is a maximal split
torus, `ν` is generic, and `StandardCocharacterStatement.{u}` holds.
`rootAssociation_levi_mem` proves

`x ∈ M_J ↔ n⁻¹ * x * n ∈ M_I`.

The proof obtains the published standard-Levi conjugation statement from
`standardLeviConjugationStatement_of_standardCocharacterStatement`, applies
`levi_map_conj_of_character_image` to the exact character-set equality, and
uses `conjugationMembership_of_map_eq`. It does not prove the
standard-cocharacter premise. With a topological group structure on the
ambient rational points, `rootAssociationLeviEquiv` packages this membership
law as a continuous multiplicative equivalence `M_J ≃ₜ* M_I`. Its application
lemma states the displayed inverse-conjugation formula on actual points.
There is no local compactness premise for this construction.

`rootAssociationEquiv_apply_character` computes the published equivalence
`I ≃ J`: the character underlying the image of a label is exactly its image
under the specified Weyl character action. The proof uses the value law of
the image-set equivalence used in the existing construction.
`rootAssociationFinsetEquiv` is the induced equivalence `Finset I ≃ Finset J`.

For every `K : Finset I`, `rootAssociation_leviIndex` proves that the same `n`
associates `leviIndex I K` and
`leviIndex J (rootAssociationFinsetEquiv K)`. Both directions are proved by
unpacking the two finite-set maps and using the character value law. In
particular no replacement normalizer representative is chosen.
`rootAssociationProperFinsetEquiv` restricts this equivalence to subsets
unequal to their respective full finite sets. The proof uses
`Finset.map_univ_equiv` and injectivity, so it also applies to empty finite
label sets and their empty proper-test families.

Finally, `rootAssociationLeviEquiv_descendant_mem` applies the earlier Levi
membership law to the descendant association. It matches the actual
descendant Levi subgroups read inside the two parent Levis by
`Subgroup.subgroupOf`, under the original parent equivalence.

These constructions use only the cited published interfaces and finite-set,
subgroup and equivalence operations. Their provenance is internal, with no
new literature theorem asserted. They do not establish matching of the
restricted unipotent radicals, preservation of cuspidality, a geometric
filtration, a datum isomorphism, or the full rational cuspidal-support
association proposition. Those remain separate obligations.
