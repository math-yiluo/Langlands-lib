# Finite projective dimension on etale valuation polynomial charts

This is an internal algebraic derivation from the imported countable valuation
dimension bound, polynomial-action resolution, flat-unramified dimension
transfer and Mathlib's finite-type and finite-presentation constructions.

`polynomialCoefficientModuleMap` is the actual `R`-linear map from a finite
polynomial-vector module to `M`: apply the supplied polynomial algebra map
in each coordinate, then apply the supplied finite free `S`-module map,
restricted to `R`. Its surjectivity theorem lifts each coordinate through
the algebra map and then uses the module-map surjection.

For any commutative ring `R`, finite-type commutative `R`-algebra `S`, and
finite `S`-module `M` with its compatible `R`-action,
`countablySpanned_of_finite_finiteType` proves `CountablySpanned R M`.
The universes of `R`, `S`, and `M` are independent. A finite polynomial
algebra surjects onto `S`, and a finite free `S`-module surjects onto `M`.
The coordinatewise polynomial quotient is an actual surjective `R`-linear
map. Its composite with the latter surjection maps the countable
coordinate-monomial spanning family onto a spanning family of `M`.

The remaining declarations take an arbitrary valuation domain `R`, a finite
variable type `σ`, and a commutative algebra `S` over `MvPolynomial σ R`.
These rings, variables and the modules in the dimension bounds lie in the
same arbitrary universe. Assume `S` is finite type over `R`, flat and
essentially finite type over the polynomial ring, and formally unramified
over that ring.

For a finite `S`-module `M` that is torsion-free over `R`, with the displayed
compatible scalar actions, the first dimension theorem gives
`PD_S(M) ≤ 1 + Nat.card σ`. The countable spanning result and the imported
valuation theorem give `PD_R(M) ≤ 1`. The polynomial-action theorem raises
the bound by the number of variables. The imported flat-unramified
theorem transfers that polynomial-ring bound to `S` through its actual
tensor-induction module retract.

For any finitely presented `S`-module `M`, the second dimension theorem gives
`PD_S(M) ≤ 1 + Nat.card σ + 1`. The compatible `R`-algebra tower is assumed
in this theorem. A finite free `S`-module surjects onto `M`, with a finite
relation kernel by finite presentation. Polynomial flatness and transitivity
make `S` flat over `R`, hence torsion-free over the domain `R`. The actual
relation kernel therefore inherits `R`-torsion-freeness from the finite
free source. The preceding bound applies to that kernel; its short exact
sequence with the finite free source shifts the bound once.

Finally, an etale polynomial chart has the required flatness, finite
presentation and formal unramifiedness. Finite type over `R` follows by
transitivity. The last theorem supplies the uniform witness
`1 + Nat.card σ + 1` to the existing predicate
`FiniteProjectiveDimensionForFinitelyPresentedModules S`.

No restriction on the rank of the valuation domain is made, and fields are
included. The numerical bound is not asserted to be optimal. Coherence,
smooth chart constructions and geometric line-bundle extension are not
conclusions of this module.
