# Zariski gluing of actual formal homomorphisms

For any set s of elements of R with Ideal.span s = ⊤, the principal
opens D(a), a in s, cover Spec R. This module constructs and uniquely
characterizes the gluing of compatible formal coordinate maps and
O-linear homomorphisms over this cover. The set s need not be finite.

`CoordinateMap.BasicCompatible` says that the actual power-series maps
over R[1/a] and R[1/b] have equal coefficient extensions to R[1/(ab)].
The two restriction maps are Mathlib's `awayToAwayRight` and
`awayToAwayLeft`. `CoordinateMap.ext_basic` proves equality from these
localizations: each coefficient is determined by its images in all
R[1/a], using joint injectivity of the localization maps.

`glueBasicCoefficient` constructs each global coefficient by Mathlib's
structure-sheaf gluing theorem
`Localization.existsUnique_algebraMap_eq_of_span_eq_top`.
Compatibility of those coefficients follows from compatibility of the
coordinate maps. `CoordinateMap.glueBasic` collects the glued
coefficients into power series. Their constant terms vanish because
their images in every localization vanish. `glueBasic_map` proves
that these series restrict to the prescribed local maps.

`ModuleLaw.basicCoefficientMap` is the structural O-algebra map
R → R[1/a]. `Hom.BasicCompatible` imposes the preceding actual
coordinate-map condition on formal O-linear homomorphisms.
`Hom.glueBasic` constructs their unique global homomorphism. To prove
preservation of formal addition and commutation with every scalar
action, it checks both coefficient identities on the cover and uses
the corresponding local identities. `Hom.glueBasic_map` and
`Hom.glueBasic_unique` give existence and uniqueness of the gluing.

The provenance is internal: the construction applies the structure
sheaf's coefficient gluing to the existing formal-series definitions.
The formal laws M and N already have global coordinates. This module
does not glue formal modules with varying coordinate charts, construct
a rational Hom sheaf, or prove local isogeny descent or moduli
representability.
