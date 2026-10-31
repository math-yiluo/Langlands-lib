# Derived comparisons from a bounded finite projective family

`Langlands.Cohomology.ModuleComplex.BoundedProjectiveFamilyDerivedComparisonStatement.{u}`
is an internal algebraic conversion interface. Let R be any commutative
ring, and let K be a family of finite projective R-modules indexed by the
natural numbers. Assume the R-linear differentials δ square to zero and
K is zero, expressed by `Subsingleton`, above a fixed natural number n.

The statement chooses one integer-indexed strictly perfect complex P
before all target complexes and all scalar rings. It asserts two
comparison properties:

- For any family C of R-modules with square-zero differentials d and a
  chain map φ from K to C, four explicit cycle and boundary tests imply
  an isomorphism from Q(P) to Q of C assembled as a natural-number
  complex and extended by zero to the integers.
- For every commutative ring A and ring homomorphism f : R → A, install
  the algebra structure given by f. For any family C of A-modules with
  square-zero differentials d and a chain map Θ from A tensor K to C,
  the analogous four tests imply an isomorphism from Q of the ordinary
  degreewise scalar extension of that same P to the extended C complex.

In both clauses the tests are injectivity and surjectivity on degree-zero
cycles, followed by injectivity and surjectivity on positive-degree
cycles modulo boundaries. They are assumptions on the supplied maps.
There is no boundedness, flatness or finiteness assumption on C. Neither
R nor A is required to be noetherian, and f is arbitrary.

All module carriers remain in universe u. Q is Mathlib's standard actual
derived localization, with morphism universe u+1; `IsStrictlyPerfect`
and `baseChange` are the existing Library definitions. The conclusion
does not assert naturality or construct geometric or right-derived
sections comparisons.

## Provenance

Workers 137 and 958 designed this interface to consume the raw module
families and scalar-dependent maps produced by the noetherian Čech
construction. This is an internal consequence of the published
`boundedNatComplexExtension` and `natModuleQuasiIsoCriterion` interfaces,
together with `DerivedPlus.mapExtendIso`. It exposes their conversion
steps without requiring a noetherian flat-complex replacement or any
unpublished geometric definition. No external theorem is assumed here,
and this statement file proves none of its comparison assertions.
