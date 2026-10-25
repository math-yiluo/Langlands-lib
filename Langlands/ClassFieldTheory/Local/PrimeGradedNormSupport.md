# Integral norm and residue support for the prime graded norm

Worker 96 authored this module. It defines `PrimeGradedNorm.integerNorm` as the
actual field norm restricted to the canonical integer rings and proves the
support facts below. It does not prove `PrimeRamifiedGradedNorm` or assume any
trace-image or norm-expansion formula.

Throughout, `F : PadicField.{u} p` and `L : PadicField.{v} p` have independent
universes and the supplied compatible scalar structures. Where required the
extension is finite dimensional, totally ramified in the explicit sense
`e(L) = [L:F] * e(F)`, and Galois. No uniformizer or residue-field
identification is chosen.

- `residue_bijective` derives bijectivity of the actual relative residue map
  from the published relative residue-degree-one result and injectivity of a
  field homomorphism. This lemma does not require a separate finite-dimensional
  instance for the extension.
- `residueDegree_eq` cancels the positive absolute ramification index and
  extension degree in the two absolute degree identities and the tower law.
- `ord_norm` and `ord_algebraMap` cancel positive residue degrees or
  ramification indices in the published norm and scalar-map order identities.
  They apply to all field elements, including zero, with the existing order
  convention.
- `norm_integral` uses the relative normalized absolute-value identity to show
  that the field norm of an integer is integral. This supplies the proof field
  of `integerNorm`; `integerNorm_coe` records its exact field value. These
  constructions do not need total ramification or Galoisness.
- `residue_norm` uses the Galois product formula for the norm. Total ramification
  makes inertia the whole Galois group. The level-zero lower-group membership
  criterion then shows that every integer automorphism fixes reduction, so the
  product reduces to the extension-degree power.
- `zero_coordinate` specializes that identity to the underlying integer units
  of source and target filtration elements whose field units are related by the
  actual norm. It is exactly the zero-coordinate equality required for the
  later graded-norm proof, conditional only on those elements and their equality.
- `degree_eq_prime_of_positive_break` uses the supplied actual lower-group
  pattern at index one. A positive break makes that group top, and the
  published prime-degree ramification criterion identifies the extension degree
  with the residue prime.

These are internal consequences of the imported arithmetic and coordinate
constructions. Their role follows the zero-level part of Jean-Pierre Serre,
*Local Fields*, V.3, Proposition 5 (printed pp.84–85 / PDF pp.91–92), registered
source `serre-1979-local-fields`. Worker 96 read V.3, printed pp.83–85 / PDF
pp.90–92 and the registered 2019 author corrections, PDF pp.2–3. No correction
affects that passage. The implementation above describes the actual Lean
proofs and makes no claim about the positive graded formulas, filtration
containments, or the literal trace coefficients.
