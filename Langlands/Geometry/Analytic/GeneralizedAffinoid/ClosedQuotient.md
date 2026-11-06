# Actual presented closed quotients and bounded quotient recognition

Worker 1685 constructs a quotient presentation for every closed ideal `J` in a
presented affinoid algebra `A`. The presentation retains `A`'s arity and arbitrary
positive polyradius and pulls `J` back through the actual weighted Tate quotient
map. No Noetherianity, strict radii, reducedness, nonzero algebra, nontrivial
valuation or coefficient completeness is needed. Completeness of the constructed
quotient over a complete coefficient field follows from the imported general
instance for presented algebras.

This is internal derived infrastructure for closed-immersion descent. It uses
the published actual weighted presentations, bounded closed-quotient descent and
admissible-epimorphism controlled-lift criterion. The source convention is
Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §1.1, printed pp.11–12 / PDF pp.25–26, registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
In particular, a closed ideal gives a normed quotient, and admissibility compares
the actual quotient seminorm with the target norm. The finite-presentation
packaging here is a derived construction, rather than a newly asserted source
theorem.

`ClosedQuotient.algebra A J` uses the closed inverse-image ideal in `A`'s original
weighted Tate algebra. `map A J` descends the new presentation map through the
old ideal. Its composite with the old presentation map is exactly the new
presentation map. Surjectivity follows by lifting a target element to a weighted
series. The quotient norm bound proves that `map` is contractive, and its kernel
is exactly `J`.

`map_isAdmissibleEpi` proves uniform controlled lifts with constant two. A
nonzero target element has a weighted-series representative with norm less than
twice its target norm; the old presentation map does not increase that norm.
Zero is lifted by zero. Thus admissibility includes both surjectivity and the
required positive two-sided quotient-seminorm comparison, and does not rely on
an open mapping theorem.

`lift` descends every bounded algebra map annihilating `J`. Its composite with
`map` is the entire original bounded map. `norm_lift_le` proves that every
supplied positive norm bound descends unchanged, using near-minimal weighted
representatives and contractivity of the old presentation. Surjectivity gives
`hom_ext`, and `boundedHomEquiv` packages the full bounded-Hom quotient property
against an arbitrary normed target algebra in an independent universe.

For an admissible epimorphism `φ : A → E` whose actual kernel is `J`,
`equivOfAdmissibleEpi` constructs a bounded algebra equivalence from the new
presentation to the unchanged target `E`. The descended map is bijective by the
kernel equality and surjectivity. Controlled lifts for `φ`, followed by the
contractive presented quotient map, bound the actual algebraic inverse. No norm
control is inferred merely from algebraic bijectivity.

This module constructs quotients of supplied closed ideals and recognizes
supplied admissible quotients. It does not prove finite ideal descent or construct
the global special-set intersection.
