# Predicates for fundamental classes in relative Galois cohomology

This pair is authored by Worker 49. It defines predicates on the actual
`relativeCohomology K L 2`, not a substitute cyclic group. The invariant
argument is only an additive homomorphism into the actual quotient
`ℚ / ℤ`; injectivity, image, arithmetic normalization, and existence are
not included in its type. No class is selected by choice.

For a finite extension `L/K`, `IsFundamentalClass K L inv c` means
`inv(c) = 1/[L:K]` in `ℚ/ℤ`, using the positive rational representative
and `Module.finrank K L`. `HasUniqueFundamentalClass` asserts the existence
of exactly one such class. `FundamentalClassGenerates` says that every such
class has exact additive order `[L:K]` and generates the entire relative
second cohomology group. These are property definitions, not proved
local-field assertions.

For a tower `K ⊆ L ⊆ M`, with all three field extensions finite and
the algebra structures satisfying `IsScalarTower`, the law predicates are:

- `FundamentalClassInflation`: for fundamental classes `c` of `L/K` and
  `d` of `M/K`, `Inf(c) = [M:L] d`. Its definition needs `Normal K L`
  to use the actual normal-restriction map on Galois groups.
- `FundamentalClassRestriction`: for fundamental classes `c` of `M/K`
  and `d` of `M/L`, `Res(c) = d`.
- `FundamentalClassConjugacy`: for a commuting square of field
  isomorphisms, the induced actual cohomology isomorphism carries one
  fundamental class to the other. Both base and extension fields can move.

The map in the inflation predicate is `relativeInflation`, constructed
from normal restriction of automorphisms and inclusion of units.
The map in the restriction predicate is `relativeRestriction`, induced by
restriction of scalars on automorphisms and the identity on the top field's
units. The conjugacy predicate uses `relativeConjugacy`, which constructs
both the Galois-group and coefficient isomorphisms and proves equivariance.
No law predicate takes an unspecified cohomology operation as a parameter.

The single-extension and conjugacy definitions retain independent
universes for the base fields and an arbitrary universe for extension
carriers. The tower definitions use one arbitrary common universe,
matching the existing cohomology-map interface. They do not reduce fields
or cohomology groups to Type 0.

Source correspondence: Jean-Pierre Serre, *Local Fields* (1979),
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
Chapter XI, §3, printed page 168 (PDF page 174).
The first paragraph defines the class with invariant `1/[L:K]` and states
its exact order and generation property. The next display gives the
inflation, restriction, corestriction, and conjugacy formulas.
The first, second, and fourth formulas are represented above.
The general local-field realization is Chapter XIII, §4, Theorem 1,
printed page 196 (PDF page 201); it must appear downstream as a conclusion.

The sign convention is Serre's arithmetic convention: fundamental
classes have invariant positive `1/[L:K]`. In Chapter XI, §3, the
fundamental class is the left factor of the Tate cup map. In degree
`-2`, that map goes from the abelianized Galois group to the norm quotient,
and its inverse is Serre's arithmetic reciprocity homomorphism.
The host's geometric reciprocity differs by inversion in the abelianized
Galois group: `rec_geom(a) = rec_arith(a)⁻¹`. In the reverse direction,
the geometric map is `theta_geom(g) = theta_arith(g⁻¹)`.
Serre's local arithmetic normalization is also explicit in XIII.4,
Proposition 13, printed page 197 (PDF page 202).
The host convention is Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique* (2000), §1.1, printed page 439
(PDF page 1): the map from the Weil group to field units sends geometric
Frobenius to a uniformizer. Retained source `henniart-2000-simple-proof`,
SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
at `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
These definitions do not change the sign of the
fundamental class to accommodate that separate convention.

This group supplies the predicates whose operations are already available.
A downstream corestriction predicate must use the genuine positive-degree transfer
being constructed in existing prerequisite task
`bc3f0bd4-2281-4247-a4b9-931c9cf179e8`, specialized to the actual Galois
subgroup. The local proposition family will existentially quantify
Worker 42's data-only invariant family and assert the class-formation
axioms, existence/uniqueness, and all four laws; it will not assume them
as hypotheses. Its absolute/relative coherence must use the genuine
finite-to-continuous comparison under existing task
`c6ea3f74-2826-48db-9ab1-46587ae2dd92`. The absence of those dependent
operations here does not replace or discharge either requirement of
the full task.

The published `Langlands.ClassFieldTheory.Local.Cohomology` module supplies
the actual relative cohomology, restriction, inflation, rational quotient, and
reciprocal class. The accompanying `Conjugacy` pair in this definition group
supplies the constructed field-square transport. The remaining operations
described above are not imported or assumed by this pair.
