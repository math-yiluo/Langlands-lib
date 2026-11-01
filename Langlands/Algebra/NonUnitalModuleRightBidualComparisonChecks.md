# Complete actual right bidual comparison interfaces

This internal companion to `NonUnitalModuleRightBidualComparison` checks
elaboration of complete unapplied declarations rather than only chosen
applications. Its provenance is the interface contract of that pair, which
explains the connection to Renard I.4.1 and the derived comparison.

The checks specify the actual second nondegenerate full-dual subtype, its right
action, both original comparison intertwiners, the recovered complex-linear
comparison, the entire naturality equation, the exact categorical composite,
its natural isomorphism and categorical naturality. Algebra and original
carrier universes are independent. Additional complete assignments use
universe pairs `(0,1)` and `(1,0)` and source/target triples `(0,1,2)` and
`(1,2,0)`.

The competing-structures section makes alternative actions and complex modules
available, then assigns the comparison using explicitly specified original,
raw and transported structures. This checks that typeclass search cannot
silently replace the stated actions or recovered complex modules. These
examples add no mathematical hypothesis to the exported construction.
