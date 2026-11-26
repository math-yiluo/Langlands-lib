# The determinant as Mellin variable of the real unequal-rank kernels

Let `t < r`. The real unequal-rank integrand `realUnequalIntegrand h W V s` lives on the left
unipotent quotient `Q_t = N_(t+1)(ℝ) \ GL_(t+1)(ℝ)`, and the dual kernel
`realUnequalDualKernel h W V s` on `Q_t × Mat_((r-t-1)×(t+1))(ℝ)`.

* `quotientDetAbs q = |det q.out|`, the absolute determinant of a representative; it is positive
  (`quotientDetAbs_pos`) and continuous on the quotient (`continuous_quotientDetAbs`), since the
  determinant descends to the quotient (upper unipotent matrices have determinant one).
* `realUnequalIntegrand_eq_mul` and `realUnequalDualKernel_eq_mul`: both kernels satisfy
  `K s = K 0 · (quotientDetAbs)^s`, because the determinant power `detPower |·| g (s - b)`
  factors as `detPower |·| g (0 - b) · |det g|^s`.
* `sigmaFinite_quotient`: the quotient measure `D.measure` of compatible quotient measure data is
  σ-finite (the quotient of the σ-compact group is σ-compact and `D.measure` is regular).
* `halfPlane_mellinData`: if a kernel `A s = A 0 · δ^s` with positive measurable `δ` is integrable
  for `Re s > σ`, then `A 0` is a.e. strongly measurable and `‖A 0‖ · δ^b` is integrable for every
  real `b ≥ σ + 1`.

These are the real counterparts of the corresponding declarations of the Library's
`ComplexUnequalMellinReduction` (where the determinant is measured by `|·|²`). They present the
unequal-rank integrals as Mellin transforms in the determinant, as in Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), Proposition 4.1 and §10.3.
