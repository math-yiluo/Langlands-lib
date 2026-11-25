# Residue comparison squares for recovered apartment tori

This derived module specializes the actual torus map in
`UnramifiedRecoveredTorusMap` along the residue coefficient square. Its
constructions work at arbitrary universe and in all characteristics on the
supplied recovered models.

`neutralResidueBaseChangeIso` first identifies the coefficient pullback of the
lower neutral special fibre with the special fibre of the actual pulled-back
neutral model. It then uses the residue pullback of the supplied neutral
recovery isomorphism to reach the actual upper neutral special fibre.

`baseChangeTorusSpecialFibreIso` is the canonical coefficient comparison for
the actual lower integral torus, packaged as its split torus model. The theorem
`baseChangeTorusSpecialFibreIso_comp_inclusion` proves equality of its composite
with the upper residue inclusion and the lower residue inclusion followed by
neutral recovery. It uses naturality of
`IntegralModel.specialFibreBaseChangeIso` on the original torus inclusion,
then composes with the residue pullback of neutral recovery.

For recovered apartment models, `apartmentTorusSpecialFibreIso` uses the
prescribed lower torus. The theorem
`apartmentTorusMap_specialFibre_comp_inclusion` specializes the actual
integral map into the prescribed upper torus. Its proof applies residue base
change to `apartmentTorusMap_comp_inclusion` and then uses the preceding
coefficient comparison square.

The construction retains both actual tori, both inclusions and the supplied
neutral recovery isomorphism. It asserts no reductive quotient, root
nonvanishing or chamber existence. Its provenance is the internal coefficient
base-change naturality and torus-map APIs; no additional literature statement
is introduced.
