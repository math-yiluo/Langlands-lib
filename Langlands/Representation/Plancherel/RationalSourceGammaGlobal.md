# Global integration on actual reductive rational points

Author: Worker 200.

This internal adapter is motivated by Waldspurger, *La formule de
Plancherel pour les groupes p-adiques* (2003), I.1, second formula (2),
printed p.240 / PDF p.6. It assembles published actual-point and
measure-theoretic results at the source's common-compact Haar scale.

The field is an arbitrary-universe nonarchimedean local field in any
characteristic. The group is an actual connected reductive group scheme,
given by `IsConnectedReductive G`, with no splitness or quasisplitness
restriction. The declarations explicitly retain `IsAffine G.X.left` and
`LocallyOfFiniteType G.X.hom`, matching the existing actual-Haar API.
These redundant geometric assumptions follow from connected reductivity;
smoothness is installed from `hG.smooth` inside each theorem. The topology and measurable space are the
canonical rational-point topology and its Borel sigma algebra. Supply a
field-defined cocharacter `chi` and a compact open subgroup `K`.

`openCellMeasure` pushes the product of the existing `parabolicHaar`
and opposite `radicalHaar` measures through the actual coordinates
`(p,v) ↦ p * v^(-1)`. Each of these subgroup Haar measures was fixed by
mass one on its intersection with `K`. Neither the measures nor the
existing indicator-defined `gamma` are chosen to force an identity.

`ambientHaar_eq_gamma_inv_smul` proves equality of measures:

`ambientHaar K hK = (gamma chi K hK)^(-1) • openCellMeasure chi K hK`.

`lintegral_eq_gamma_inv_mul` proves the corresponding iterated integral
formula for every measurable nonnegative extended-real function, first
over the actual parabolic and then over the actual opposite radical.

Both proofs derive the premises of the published global integration
engine. Closedness of the actual subgroups supplies local compactness;
second countability is inherited from the ambient rational-point group.
The published actual open-cell theorem supplies the open embedding.
`rationalDynamicOpenCellConull` proves the null complement for this
group, cocharacter and ambient Haar measure. The already proved radical
translation theorem supplies ambient right invariance along the opposite
radical. Finally, `ambientHaar_self` makes the compact mass exactly one.
The global engine therefore uses precisely the original gamma inverse.
No conullness, embedding, chart, ambient unimodularity or integration
formula is supplied as an additional hypothesis.

This is an actual two-factor rational-point specialization and a measure
identity. The source prints the three-factor `U,M,opposite U` formula
with the inverse parabolic modulus. The comparison with those source
coordinates uses the separately published semidirect Haar normalization
and retains its compact-limit stability premise. The scalar identification
with the source Iwasawa-modulus integral additionally retains the existing
factorization and Levi right-invariance premises. This module does not
realize a special compact, prove arbitrary same-Levi independence, or
establish a Bochner formula or any Plancherel conclusion.
