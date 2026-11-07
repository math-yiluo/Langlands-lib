# Principal irreducibility neighborhoods from compact compression

Worker 452. This internal assembly combines actual compact-average
compression and coefficient specialization with Worker 1444's localized
determinant witness. It implements a conditional step of Renard,
*Représentations des groupes réductifs p-adiques* (9 July 2026),
VI.8.4 Proposition proof, printed pp. 192–193, PDF pp. 198–199.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`IsFullSpecialization S A χ D` says that the complex evaluation
`χ : S →ₐ[ℂ] ℂ` has an actual intertwiner from `A` to `D`, respecting
evaluation of coefficient scalars, whose full scalar extension is
bijective. It uses the algebra structure on `ℂ` determined by `χ`.
No particular intertwiner is chosen as part of the public data.
`exists_fixedBasis` uses such a witness to transport a coefficient basis
of the actual `K`-fixed vectors of `A` to a complex basis of the actual
`K`-fixed vectors of `D`. In that basis the actual compression matrices
are the evaluated coefficient matrices.

For `S` a principal localization of a commutative complex algebra `B`
at `g`, `exists_regular_principal_neighborhood` takes a finite coefficient
basis of the fixed vectors of `A`, a parameter family of complex
characters of `B` and actual smooth fibers, full specialization at
each parameter where `g` does not vanish, and detection by the same
compact open `K` of every irreducible actual subquotient of every fiber.
If the fiber at a parameter where `g` is nonzero is irreducible, it
produces one element of `B`, nonzero there, whose nonvanishing forces
irreducibility of every fiber in the family.

The proof first specializes the coefficient basis at the initial fiber.
Detection applied to that irreducible fiber as its own subquotient gives
a nonzero fixed vector. Its fixed basis therefore has a nonempty index
type. The forward compact-compression comparison makes the initial
matrix family irreducible. The localized determinant theorem then gives
a regular witness retaining the nonvanishing of `g`. At every parameter
where that witness is nonzero, full specialization again transports the
same coefficient basis. Its nonempty index type proves that this fiber
is nonzero. The converse compact-compression comparison, using the
supplied detector, proves irreducibility of the fiber.

`exists_polynomial_principal_neighborhood` specializes the parameter
space to the actual unramified characters of a connected reductive group
scheme `M` over a nonarchimedean local field, with the canonical topology
on `M(F)`. The characters of `B` are `coefficientCharacter M e`, obtained
from a supplied complex-algebra equivalence `e` between `B` and the actual
regular functions on those unramified characters. Under the same basis,
full-specialization and uniform detection inputs, it produces a polynomial
in the published canonical coordinates. Its principal open set
`rationalUnramifiedPrincipalOpen M hM p`, the form used in the published
VI.8.4 statement, contains the initial character, and every fiber over it
is irreducible. The proof applies the regular theorem above and replaces
the regular witness by Worker 1444's `rationalRegularPolynomial`, whose
principal open set is exactly the nonvanishing locus of that witness.
The smooth fibers may be representations of any topological group; here
they are not required to be representations of `M(F)` or its induced
representations.

All group, coefficient, localization, carrier, parameter and matrix-index
universes are independent. The basis, specialization, compatibility and
uniform detection requirements remain explicit. This module neither
constructs the universal induced family nor proves those structural
requirements, and it does not prove the closed
`InducedIrreducibilityOpenStatement`. Its provenance is the imported
compact-compression, fixed-vector scalar-extension and localized
determinant proofs. The latter's polynomial supporting construction
retains Worker 1664's original monomial-clearing attribution.
