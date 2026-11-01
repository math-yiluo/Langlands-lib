# All-integer products and finite binomial formulas on actual blocks

Statement prepared by Worker 709; source and interface checks and documentation
completed by Worker 345. This proposition supplies no proof. Its
actual construction is imported from the published
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock` module.

For arbitrary natural `d`, finite-dimensional complex `V : Type u`, actual
commuting invertible tuple `A`, unit labels `c` and every
`n : Lattice d = Multiplicative (Fin d → ℤ)`, write `W` for the actual
generalized-weight block, `ρc` for its actual restricted representation,
`G_i` for its genuine generator units, `U_i` for its normalized units,
`N_i = U_i - 1` and `χc = coordinateCharacter c`. Here `W` is exactly
`generalizedWeightBlock A c`, the intersection of the maximal generalized
eigenspaces of the tuple entries for the complex values of `c i`. The
restricted representation is `generalizedWeightBlockRepresentation A c`,
the units are `generalizedWeightBlockGenerator A c i` and
`normalizedBlockGenerator A c i`, and the difference is the actual
`normalizedGeneratorDifference A c i`. These objects are imported unchanged;
no independently supplied block, restriction or normalization occurs.
`Langlands.CommutingTupleGeneralizedWeightProductStatement` states the
following three endomorphism equalities:

```text
ρc(n) = product_i (G_i ^ n_i)
ρc(n) = χc(n) • product_i (U_i ^ n_i)
ρc(n) = χc(n) • product_i
  (sum_{0 ≤ k < finrank ℂ V} Ring.choose (n_i : ℂ) k • N_i ^ k).
```

Each product is the `List.prod` of `List.ofFn`, in increasing `Fin d`
order. The powers in the first two equations are integer powers in the
genuine endomorphism unit group and are then coerced to endomorphisms.
The final powers are natural powers of the actual differences. The
scalar character is coerced from its unit value to a complex number.
Commutativity of the constructed factors will justify comparison with the
published ambient representation's `Finset.noncommProd` formula; the
ordered list makes the proposition itself independent of a supplied proof
of that commutation.

The binomial coefficient is the polynomial coefficient `Ring.choose`,
evaluated at the complex cast of the integer coordinate. Negative and
mixed-sign tuples are included. No nilpotence, decomposition, basis,
product law, nonzero block or positivity hypothesis is supplied by the
caller. A future proof should use actual block nilpotence and the
published integer-unipotent binomial theorem, rather than proving that
generic expansion again.

At `d = 0`, all products are empty and equal the identity. At zero `V`,
the truncation bound is zero and each binomial factor is an empty sum;
on every zero block the identity endomorphism equals zero, so this is
consistent, including when the product itself is empty. Zero blocks for
other labels are retained. The carrier universe is arbitrary.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, Appendix C.III, printed p.280 / PDF286, all three lines of
the displayed expansion of `A_j(n)`. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF285–286 were read directly for this draft. This is a derived basis-free
formulation of those matrix identities, with the explicit
ambient-dimension truncation requiring the separate actual nilpotence
bound in a future proof. The source writes a finite series with ellipses;
`Finset.range (Module.finrank ℂ V)` makes its bound explicit. The basis-free
block definition, all unit labels (including zero blocks), zero-based `Fin d`
indexing, ordered `List.ofFn` products and this truncation are derived
formulation details. This statement does not assert a decomposition or
construct a common triangularization basis. The whole generator is raised to its integer exponent, as in the
governing 2026 display.

The registered supplementary errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. The old p.322 line -4 correction places the entire
scalar-times-unipotent factor inside the power; that grouping is already
present in the 2026 source and is retained through the actual units here.

The declaration is a closed `def : Prop` at universe `u`: all mathematical
inputs, including `d`, `V`, its additive and complex vector-space structures,
finite-dimensionality, the tuple `A`, labels `c` and the integer lattice point
`n`, are quantified inside its body. Its three equalities are joined by
conjunction. Proving the definition is a separate obligation; defining it
provides no inhabitant or theorem establishing any of the three equalities.
