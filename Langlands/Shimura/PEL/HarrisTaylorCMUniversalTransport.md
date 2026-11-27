# Polarized rational transport of the universal CM families

A transporter of represented small CM levels induces an actual scheme map.
On a connected component of the source, `cmUniversalLevelSource` pushes
its chosen universal representative's frame orbit along the transporter.
`cmUniversalLevelTarget` transports the target representative's frame to
the image geometric point and pulls the polarized abelian scheme and orbit
back along the actual component map. The path is an isomorphism of finite
étale fibre functors over the target component. The proof of geometric path
existence supplies a choice of such a path.

`CMUniversalLevelTransport` records a rational isomorphism between these
actual abelian schemes over the source component. It intertwines the PEL
algebra actions. Pullback takes the target polarization to the source
polarization multiplied by a specified rational unit. The induced transport
on the target-level frame orbit identifies the pushed source orbit with the
pulled-back target orbit. `cmUniversalLevelTransport_nonempty` applies
`cmUniversalRepresentative_transition` at the chosen source point and
extracts the rational isomorphism, multiplier and orbit equality from the
actual quotient relation. `cmUniversalLevelTransport` chooses such a witness.
Both legs of the Hecke span are instances of this construction.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp. 90–91 (PDF pp. 98–99), gives the underlying
rational polarized equivalence and the change of frame for Hecke maps. The
construction uses that equivalence over the actual component via the Yoneda
transition of the universal classes. Literature ID
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
