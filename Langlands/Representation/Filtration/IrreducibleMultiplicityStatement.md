# Actual composition series and multiplicities of an irreducible object

This pair states an elementary algebraic adapter for actual representation
filtrations. The wrapper is `Langlands.IrreducibleMultiplicityStatement` in
`Langlands.Representation.Filtration.IrreducibleMultiplicityStatement`.
The coefficient field, the acting monoid, the irreducible object's carrier and
the specified constituent's carrier have independent universes `uK`, `uG`,
`uA` and `uT`.

## Statements

`IrreducibleCompositionSeriesStatement` quantifies over an arbitrary field
`k`, monoid `G`, and representation `A`, and assumes that `A.ρ` is irreducible.
It asserts the existence of an actual `ObjectRepFiltration A 1` whose only
graded quotient is irreducible, together with a representation equivalence
from that actual quotient to `A.ρ` (packaged by `Nonempty`). It thus supplies
an actual one-factor composition-series witness, not just numerical module
length one.

`IrreducibleJordanHolderMultiplicityStatement` also quantifies over an
arbitrary representation `τ` and natural number `m`. It asserts

```
HasJordanHolderMultiplicity A τ m ↔
  (Nonempty (A.ρ.Equiv τ.ρ) ∧ m = 1) ∨
  (¬ Nonempty (A.ρ.Equiv τ.ρ) ∧ m = 0).
```

No irreducibility assumption on `τ` is imposed. In particular, an object
equivalent to `A` has multiplicity one, and every other object has
multiplicity zero. Each multiplicity assertion retains the actual finite
composition series required by `HasJordanHolderMultiplicity`; existence is
not replaced by an equivalence of two potentially false existence predicates.
The forward direction also excludes any other numerical multiplicity.

`IrreducibleMultiplicityStatement` is the conjunction of these two clauses.
There is no finite-dimensionality, group-inverse, smoothness, admissibility,
or nonzero-rank premise. Irreducibility already excludes the zero object.

## Provenance and intended derivation

These are internally derived algebraic statements, not a transcription of a
numbered result in the representation-theoretic literature. Their meanings
come from the published `ObjectDefinitions` and `MultiplicityStatement`:
actual invariant zero-to-full chains, actual quotient representations,
irreducible graded factors, and the cardinality of the subtype of matching
factor indices.

The published construction `LengthTwo.oneStep` gives the zero-to-whole chain.
Its quotient by zero is equivalent to the original representation. The
irreducibility hypothesis makes this a composition series. Counting the
singleton factor-index type then gives one or zero according to equivalence
with `τ`; the published `jordanHolderMultiplicityIndependence` compares this
count with every other actual composition-series witness. This paragraph is
a proof plan; this statement pair does not claim to prove either clause.

The adapter supplies a positive count-one witness usable in later additive
arguments. It asserts no normalized induction or Jacquet comparison, no
support map, no second adjointness, no continuation or tempered-exponent
argument, and no relative recovery or Langlands classification theorem.
