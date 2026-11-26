# Actual semistandard orbit packets from open full domains

`OrbitPacketData.conditionalOfOpenFullDomains` assembles the actual scalar
inputs of semistandard synthesis from the two open, nonempty full
convergence domains. The displayed compact and the two Iwasawa products
are for the literal same rational-point ambient group. The inducing
representation is pulled back to the cocharacter centralizer through
`CocharacterPresentation.literalLeviHomeomorph`. The supplied quotient
Haar and square-integrability property are for the actual image of the
displayed split component in this centralizer.

`forwardContinuationOfOpenFullDomain` and
`reverseContinuationOfOpenFullDomain` apply to the original standard
integrals on their entire domains. Finite length follows from
irreducibility of the pulled-back representative. The existing
`DynamicInducedOrbit.DensityPackage.ofSquareIntegrable` derives the
nonempty open irreducibility locus and the regular inverse composition
scalar on the full unitary parameter group. Its fields supply precisely
the packet data used by `OrbitPacketData.packetLinear`.

This is a derived construction for Waldspurger's IV.1 continuation
and IV.3 composition scalar, printed pp. 278–283 and 285–287
(PDF pp. 44–49 and 51–53), and for the use of the inverse scalar in the
V.2 density and VI.3 wave packet.
The openness and nonemptiness premises concern the full domains of the
original integrals. [Original publication](https://doi.org/10.1017/S1474748003000082)
