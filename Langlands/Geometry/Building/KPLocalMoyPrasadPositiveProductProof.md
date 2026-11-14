# Positive-depth sign product over the maximal unramified field

The theorem `MaximalUnramified.localMoyPrasadPositiveProduct` proves exactly
`MaximalUnramified.LocalMoyPrasadPositiveProductStatement`, at arbitrary
universe `u`. It uses the published `BuildingData.moyPrasad` and
`BuildingData.rootFiltrationSpan` without changing their definitions. The
only added assumption is `LocalTorusCommutatorFriendly`, which unfolds to
the explicit commutator clause in the target.

The implemented proof combines local constant-depth block exchange with
`KPLocalMoyPrasadGlobalExchange`. The integer-valued extended affine roots
satisfy AS2 using `exists_order_eq_one F`; their derivative roots are the
actual relative-root forms. This supplies the geometric hypotheses of the
global exchange helper over `UnramifiedClosure F`.

The actual torus-depth image normalizes each root-depth filtration, hence
each selected span and the original sharp filtration. Local exchange of
opposite blocks moves its torus factor to the right. Global exchange then
covers the sharp group by the negative span, positive span and torus image.
The generated Moy–Prasad subgroup is the product of that torus image and
the sharp group, because of normalization. Commuting the torus image past
the sign spans and absorbing two torus factors gives the negative span,
torus image and positive span. The reverse inclusion follows because all
three factors belong to the originally generated subgroup.

Finally, `depthRootSpan_eq_rootFiltrationSpan` identifies the auxiliary
subtype-indexed supremum with the published membership-indexed supremum.
This is equality of the same generated subgroup, with no additional
factorization assumption. The root blocks in the exchange retain their
ordinary and doubled-root factors, including in nonreduced systems.

This derived proof adapts the final assembly in the published
`MoyPrasadGlobalExchange` to the actual K-level torus filtration. Its source
motivation is the constant-positive-depth torus-filtration variant of KP
Lemma 7.3.11 and Proposition 7.3.12 described in the target's Markdown. No
S2 or whole S1 premise, apartment axiom, building axiom, or local-field
structure on `UnramifiedClosure F` is added.
