# Local saturation of a submodule presheaf

This derived helper constructs the actual submodule subsheaf of an ambient
module sheaf whose sections locally belong to a specified submodule presheaf.
The construction uses covering sieves. Closure under addition uses the
intersection of two covering sieves; closure under scalar multiplication
uses the same covering sieve and semilinearity of restriction. Restriction
stability follows from subfunctor saturation, and local membership follows
from the transitivity axiom for covering sieves.

`le_localSaturation` includes the original section submodules.
`mem_localSaturation_iff` identifies membership on a topological open-set
site with membership after restriction to a neighborhood of each point.
No preservation or representability assumption is added.
