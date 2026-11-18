# Actual finite torsion of relative multiplicative-type groups

This internal construction completes the finite torsion interface for the existing
`RelativeMultiplicativeType.IsMultiplicativeType` predicate. For every scheme `S`
in an arbitrary universe, a group scheme `H` satisfying that predicate, and a
natural number `n`, `hH.torsion n` is the existing scheme-theoretic kernel of
integer multiplication by `n` on the original group. Its commutative structure is
obtained from `hH.commGroupScheme`, by descent from the splitting cover. No
additional commutativity hypothesis is required of the caller.

`torsion_eq_kernel` and `torsionι_eq_kernelι` are exact identifications with the
published multiplication kernel and its inclusion. The all-test universal
property `existsUnique_torsion_lift_iff` says that a section factors uniquely
through this inclusion if and only if its natural `n`th power is the identity.
It specializes the published integer-torsion universal property using
`zpow_natCast`. Separatedness of a relative multiplicative-type group makes its
unit section closed, and the published kernel construction then proves
`torsionι_isClosedImmersion`.

For `n > 0`, `IsDiagonalizable.torsion` uses the published actual torsion model
`D_S(M/nM)`. The full quotient `M/nM` is finite because `M` is finitely generated;
therefore it is also finitely generated and gives a diagonalizable presentation.
`torsion_isMultiplicativeType` uses these presentations over the original fppf
splitting cover and the published actual torsion base-change comparison.
`torsion_isFinite` specializes the published `torsion_geometry` theorem, which
descends finiteness from the same finite full character models.

`torsionBaseChangeIso` is an actual group-scheme isomorphism for every base change
`b : S' → S`. It is exactly the published torsion comparison, which derives from
`kernelBaseChangeIso` and compatibility of multiplication with base change.
The forward and inverse inclusion equations are both proved. The defining group
and inclusion, the universal property, closedness and base-change comparison
exist for every natural `n`; finiteness and multiplicative type are asserted for
`n > 0`.

The derivation uses the published actual torsion and diagonalizable character
constructions and their fppf descent results, together with the published descended
commutativity in `RelativeMultiplicativeTypeLocality` and separatedness in
`RelativeMultiplicativeTypeGeometry`. It retains all character torsion,
including nonsmooth finite group schemes when the residue characteristic divides
`n`. It assumes neither invertibility of `n` nor any nonemptiness, Noetherian,
reducedness or characteristic condition on the base.
