# Ordinary marked Harris actions and base change

An ordinary polarized datum of the Harris dimension and an actual integral
action satisfying the full Rosati and determinant equations on a nonempty
test give the positive polarized action `harrisOrdinaryJointAction`.
Its integral restriction `harrisOrdinaryJointActionRestriction` is the
given order action, since the rational extension agrees on the full order.

The canonical abelian-scheme comparison between the direct and successive
pullbacks intertwines the actual order actions. It agrees with
`Datum.pullbackCompIso` on the underlying abelian schemes, so it identifies
the polarizations and carries the ordered levels to one another.
`harrisOrdinaryJointAction_marking_iff_restrict` applies marking
invariance under this isomorphism and the original principal marking
comparison under base change. The existence of an ambient adelic frame
needed by the successive polarized pullback is obtained from the
compatible marking on either side, using the ambient frame equivalences
for base change and the direct-to-successive isomorphism.

For a connected locally noetherian test at a principal congruence level,
`harrisOrdinaryJointMarkingCompatible_iff_point` compares the condition at
any two geometric points. It uses the actual finite étale torsion
comparisons and the principal-level comparison of invariant orbits.
`harrisOrdinaryPointwiseMarking` requires compatibility at all geometric
points. It therefore applies to disconnected and empty tests as well.
`harrisOrdinaryMarkedActionSubfunctor` applies the restriction comparison
to this condition on the actual order actions and their equations.

This is the relative version of the normalized principal marking
condition used in the PEL data. Its definition and its pullback comparison
use the same positive involution and determinant condition as the
normalized Harris data.
