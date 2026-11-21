# Descent of a relative wave packet to `[G]`

`Langlands.Global.RelativeWavePacketDescentStatement` is a proposition
definition. Under the actual adelic, root presentation, inducing form and
Iwasawa data in `IsRelativeWavePacket`, take the connected reductivity of
`G` and the identification of `U` with the geometric unipotent radical of
`P`. Then any relative wave packet `Θ` is left invariant under the actual
subgroup `A_G G(F)`, namely `RestrictionSplitCentre.canonicalRationalSubgroup`.
In particular `Θ` evaluated at the chosen representative of the class of `g`
in `RestrictionSplitCentre.CanonicalQuotient` equals `Θ(g)` at every `g`.

This is a derived pointwise compatibility for Getz–Hahn, *An introduction
to automorphic representations* (2024), §2.6, (2.20)–(2.22), pp.68–69
(PDF pp.85–86), and §10.5, (10.21)–(10.24), pp.281–282 (PDF pp.293–294): the
relative packet expression, implemented on actual adelic points, defines a
function on the quotient used for the spectrum. Its source ingredients are
the defining rational coset sum of Bernstein–Lapid (2024), §2.2, (2.1),
p.191 (PDF p.5), and the split-component transformation law for the inducing
forms of Lapid (2011), §2, p.311. The relative parameter space is the existing
annihilator of the logarithmic image of `A_G` through `P`. The packet predicate
already supplies the scalar continuation on a domain containing the imaginary
parameters; the statement does not assert the existence or holomorphy of such
a continuation. It also does not assert measurability, square integrability,
orthogonality or density of the descended function.
