# Finiteness of rational classes meeting a compact adelic regular elliptic set

`Langlands.TraceFormula.generalLinearEllipticClassFiniteness` proves
`Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessStatement` for the
actual rational and adelic matrix groups over a number field.
[Statement](GeneralLinearEllipticClassFinitenessStatement.md)

## Lean proof

- The proof takes the characteristic coefficients of an adelic matrix unit
  from degree zero through degree `n`. Each coefficient evaluates a universal
  multivariate polynomial in the matrix entries
  (`Matrix.charpoly.univ_coeff_eval₂Hom`). Entry evaluation is continuous in the
  unit-group topology, so `MvPolynomial.continuous_eval` gives a compact
  coefficient image of `Ω`.
- `principalAdeles_isClosed` and `principalAdeles_discreteTopology` give a
  closed embedding of the finite product of the principal adeles and make
  that product discrete. The inverse image of the compact coefficient image
  under this embedding is therefore finite. Rational polynomials of degree
  at most `n` inject into the principal coefficient vectors by
  `NumberField.AdeleRing.algebraMap_injective` and polynomial extensionality.
  Each qualifying rational matrix has characteristic polynomial of degree
  `n`, and its coefficient vector belongs to the compact image by
  `Matrix.charpoly_units_conj'` and `Matrix.charpoly_map`.
- The composite of `AdelicGL.finite` and `FiniteAdelicGL.localProjection`
  preserves conjugation. On rational matrix entries this composite is the
  coefficient embedding into `FiniteCompletion K v`. The characteristic
  polynomial of the projected conjugate is thus the rational characteristic
  polynomial mapped to the completion. Its separability and irreducibility
  descend by `Polynomial.separable_map` and
  `Polynomial.Monic.irreducible_of_irreducible_map`. These two properties
  give `IsRegularElliptic` for the rational element.
- For each of the finitely many polynomials, `matrixCharpolyFiniteConjugacy`
  supplies a finite set of matrix representatives. The inverse image of this
  set under the injective map `Units.val` is a finite set of rational matrix
  units. A conjugate `g * γ * g⁻¹` belongs to this inverse image whenever its
  underlying matrix is a representative. Taking `y = g⁻¹` gives the
  conjugation in the statement. The union of the finite sets of units gives `R`.

## Relation to the sources

The compactness argument specializes the strategy of Getz–Hahn, Lemma 17.7.11,
printed pp. 461–462, to characteristic coefficients. That lemma uses the
compact image in an adelic affine quotient and the closed discreteness of the
rational points of that quotient. The Lean proof uses a finite product of
adele rings for the invariant values, then obtains rational conjugacy
representatives from the Library's fixed-polynomial finiteness theorem.
Getz–Hahn's Lemma 18.2.6, Theorem 18.2.5 and Corollary 18.4.1 place the
finiteness argument in the trace formula setting. The registered source is
`getz-hahn-2024-automorphic-representations`.
[Getz–Hahn, *An Introduction to Automorphic Representations* (2024)](https://doi.org/10.1007/978-3-031-41153-3)

The local descent step implements the implication in Deligne–Kazhdan–Vignéras,
Appendix A.1.b, printed p. 43, that regular ellipticity at one place
ensures global regular ellipticity and restricts the rational classes meeting
a test function's support. The Lean proof expresses the implication in terms
of characteristic polynomials and gives the representatives in the full
group `GL_n(K)`. The registered sources are `bdkv-1984-representations-local-field`
and its readable copy `provided-8e5449fd355198877b9325b8089bb8bda8acedd0aad6ac4d1be2c08e09c64b20`.
