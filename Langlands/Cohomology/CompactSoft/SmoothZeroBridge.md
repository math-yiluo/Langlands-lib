# Reducing smooth Godement c-softness to coinduced stalk families

Author: Worker 865. This is an internal bridge toward
`Langlands.Cohomology.SmoothGodementZeroCSoftStatement`, not its unconditional
proof. All carriers belong to a common arbitrary universe `u`. The hypotheses
are exactly those of that target: a commutative coefficient ring, a topological
group acting by continuous individual translations on a locally compact
Hausdorff space with `HasStableNeighbourhoods`.

`smoothCoinducedZeroIso F` is an isomorphism of ordinary module sheaves. Its
domain is the underlying sheaf of the smooth part of coinduction of the
underlying arbitrary stalk-family sheaf `Godement.zeroSheaf F.obj`. Its codomain
is formed in the same way from the published ordinary Godement degree-zero
sheaf of the underlying sheaf of `F`. The definition carries the published
`Godement.zeroIso` through coinduction, the smooth-part functor, and forgetting
equivariance. It requires only the hypotheses needed by those functors; the
Hausdorff and local compactness hypotheses are used by the target below.

`smoothGodementZeroCSoft_of_coinducedZero` assumes, for every equivariant sheaf
`F`, c-softness of the ordinary sheaf underlying the smooth part of the
coinduction of the underlying arbitrary stalk-family sheaf `Godement.zeroSheaf
F.obj`. It concludes the published target.

The proof applies `smoothCoinducedZeroIso` to the equivariant sheaf underlying
a smooth sheaf `M`. The domain is the sheaf
in the assumption and the codomain is definitionally the underlying sheaf of
`smoothZeroFunctor M`. The published `IsCSoft.of_iso` transports the assumed
c-softness. No property of the comparison beyond its being an isomorphism is
required. The antecedent is still an explicit proof obligation; this module
provides no identification of coinduction with indexed-family coordinates.
