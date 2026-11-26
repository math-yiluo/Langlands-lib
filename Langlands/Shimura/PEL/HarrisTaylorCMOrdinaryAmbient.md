# Ordinary polarized full-level moduli over the Harris base field

`OrdinaryCMFieldModuliRepresentation` records an ordinary polarized
full-level representer over a characteristic-zero field `F`. Its point
functor is on all locally noetherian schemes over `Spec F`, with actual
maps over `Spec F`. `ordinaryFieldTestFunctor` views each of those schemes
as a `LevelBase m`: the image of the positive integer `m` is a unit in
its global sections via the field structure map.

Given an ordinary fine representer over `Spec ℤ[1/m]` with a quasi-compact
structure morphism and a projective-space immersion,
`ordinaryCMFieldModuliRepresentation_of_fineModuli` constructs its pullback
to `Spec F`. An over-`F` point of the pullback gives a map to the original
representer by the first projection. In the other direction, a map to
the original representer and the test's map to `Spec F` form a compatible
pair because any two maps to `Spec ℤ[1/m]` coincide. The pullback universal
property gives the inverse. These operations commute with
precomposition and hence give the natural isomorphism with the ordinary
moduli functor restricted by `ordinaryFieldTestFunctor`. The new
immersion and quasi-compact structure morphism follow from stability
under base change and the polynomial projective-space base change.

The resulting scheme is locally noetherian since its structure morphism
is locally of finite type. `universalDatum` picks an actual representative
of the ordinary class of its identity map. The naturality equality
`represents_hom_apply` says that each test map classifies the actual
pullback of that same datum. Thus the ambient family, its polarization,
and its ordered sections are available over the base-changed scheme.

`exists_eventualOrdinaryCMFieldModuliRepresentation` applies the construction
under `LargeLevelRepresentabilityStatement`, with the eventual bound of
that statement. Kottwitz, *Points on Some Shimura Varieties over Finite
Fields*, §5, printed p. 391 (PDF p. 19), uses an ordinary polarized moduli
space as the base for relative representability of the action in his PEL
problem. The result here gives the characteristic-zero base change on
the Library's actual ordinary functor. The ring `ℤ[1/m]` is its
full-level base. The published `LargeLevelRepresentabilityStatement`
specifies the ordinary geometric existence used here.

Source `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`,
§5, printed p. 391 (PDF p. 19), for the ordinary ambient moduli step.
