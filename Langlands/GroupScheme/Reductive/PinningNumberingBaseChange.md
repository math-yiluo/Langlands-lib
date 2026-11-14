# Numberings of scalar-extended split pinnings

This derived internal construction transports a supplied numbering of the simple
vertices of an actual split pinning along its algebraic scalar extension. The
numbering is composed with the inverse of `baseChangeSimpleEquiv`, so it takes
the same value on each transported vertex. The Cartan comparison follows from
`SplitRootDatum.baseChange_pairing` after the roots and coroots are identified by
the existing pinning scalar extension. No numbering or root datum is constructed
without the supplied split pinning, numbering, and Cartan equality.
