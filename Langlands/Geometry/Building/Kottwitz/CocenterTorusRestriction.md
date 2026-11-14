# Cocenter restriction to a maximal torus

`Langlands.Geometry.Building.Kottwitz.cocenterTorusRestriction a c` is the actual homomorphism from the chosen maximal torus to the cocenter: `Additive.ofMul (a.inclusion ≫ c.quotient)`.

This definition is extracted unchanged from `CocenterSurjectivityReduction`. The cocharacter-kernel module reuses it through `Cocenter.torusMap`, whose two arguments are in the reverse order.
