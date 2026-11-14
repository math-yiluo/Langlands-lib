# Isomorphism transport and independence of zero subgroups

For a nonarchimedean local field `F` and groups `H`, `H'` over
`K = UnramifiedClosure F`,
`UnramifiedZeroDatum.isoTransport E f` transports a supplied
`UnramifiedZeroDatum F H` through an isomorphism `f : H ≅ H'`.
It retains the torus, splitting field, derived group and simply connected
cover. It composes the torus and derived-subgroup inclusions with `f.hom`
and transports their validity proofs and connected reductivity. This
generalizes the published automorphism construction
`UnramifiedZeroDatum.transport` to different ambient groups.

The associated lemmas prove:

- `zeroPoints_isoTransport`: the transported zero subgroup is the image of
  `E.zeroPoints` under `rationalPoints.map f.hom`.
- `map_zeroPoints_eq_of_iso`: that image equals `E'.zeroPoints` for every
  supplied datum `E'` on `H'`.
- `map_mem_anisotropicZeroPoints_of_iso`: an isomorphism of groups over `F`
  maps the preimage of the upstairs zero subgroup into the corresponding
  preimage for every supplied upstairs datum on the target.
- `ZeroSubgroupDatum.zeroSubgroup_le_of_datum` and
  `zeroSubgroup_eq_of_datum`: any two downstairs zero data for the same
  group define the same zero subgroup, even if they use different maximal
  split tori, centralizer presentations, covers and upstairs data.

All these results are unconditional on the supplied data. There is no
building-existence or zero-descent premise.

The first image identity uses the published isomorphism invariance of the
simply connected image and the image of a subgroup join. The torus norm
subgroup is unchanged before applying the transported inclusion. The
published `unramifiedZeroPointsIndependence` then identifies the images
for arbitrary target data. Naturality of scalar extension gives the
anisotropic preimage assertion.

For downstairs independence, rational conjugacy identifies the two maximal
split tori. The represented-centralizer isomorphism induced by that inner
automorphism transports their centralizer zero subgroups by the preceding
preimage assertion. Cover independence identifies the ambient simply
connected images. The published normality theorem
`ZeroSubgroupDatum.normal_zeroSubgroup` removes the inner conjugation.
Applying the resulting inclusion in both directions proves equality.

This is derived infrastructure for the quantification over every zero datum
in `UnramifiedZeroDescentStatement`. It does not prove that target. Its
provenance is the existing Library constructions and the published proofs
of upstairs datum independence, rational maximal-split-torus conjugacy,
cover independence and downstairs normality. The mathematical context is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 2.6.23
and Lemma 2.6.24, printed pp. 104–105 / PDF pp. 135–136, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The Lean proof implements the
composition described here.
