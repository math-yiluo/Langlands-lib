# One dilatation lowers the defect of the points through its centre

- `AffineChart.pointAlgHom`, `TestPoint.defect_eq_pointDefect`: the defect of a test point is the
  `pointDefect` of the corresponding `R`-algebra map from the chart ring.
- `chartPrimes`, `vanishingIdeal_centre_eq`, `chartPrimes_spec`, `chartPrimes_isPrime`:
  `chartPrimes f C E` is the set of primes `ψ⁻¹(𝔪)` of the members `ψ` of `E` whose closed points
  lie in the chart `C` but not in the smooth locus; the ideal of the centre on `C` is their
  intersection, and each is the prime of an `R`-algebra map to a discrete valuation ring of
  ramification index one, as required by `DilatationDefectStatement`.
- `TestPoint.defect_ne_zero`: for `f` locally of finite type with smooth generic fibre, a test
  point outside the smooth locus has non-zero defect (from `DefectZeroSmoothAtStatement`).
- `lt_of_lt_of_lt_succ`: an arithmetic step in `ℕ∞`.
- `dilatation_step`: let `f` be locally of finite type with smooth generic fibre. Given an affine
  open `U` and a family `E` of test points with defects `< n + 1` all of which specialize into `U`
  (their closed points lie in `U`), such that the centre of `E` is smooth over the residue field on
  `U` with free restricted differentials, the blow-up of the centre (from `BlowupChartStatement`)
  is proper, an isomorphism away from the centre, and every lift of a member of `E` whose closed
  point lies in the centre has defect `< n`. The defect drop on the chart `U[J/ϖ]` is
  `DilatationDefectStatement`.

This is Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.4, Lemma 1 (printed p. 71), with §3.3,
Proposition 5 as the key input.
