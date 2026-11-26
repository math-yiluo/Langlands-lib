# Compact integration in full opposite-unipotent coordinates over the real field

`groupTranspose g` is the transpose of an invertible real matrix, written as the inverse
transpose of `g⁻¹` (`groupTranspose_val`, `continuous_groupTranspose`, `groupTranspose_mul`).
`realEntryLebesgue m` is `entryHaar` for the standard real Lebesgue measure on each strictly
upper entry of the upper unipotent subgroup `N_m`.

`RealModulusOpenCellStatement` says: for every rank `m` there is a constant `c > 0` such that
for every smooth function `F` on `GL_m(ℝ)` that is covariant for the modulus character of
the upper Borel subgroup (`IsModulusCovariant F`),

* `u ↦ F(uᵀ)` is integrable on `N_m` for `realEntryLebesgue m`, and
* `∫_{O(m)} F(k) dk = c · ∫_{N_m} F(uᵀ) du`, with the normalized Haar measure `haarK m` on
  `O(m)`.

`realModulusOpenCell` proves it.

## Proof

Integrability: the open-cell convergence theorem of the Library
(`RealGodementOpenCellConvergence`) at the modulus parameters bounds `F` on the opposite
cell; the Weyl reflection `transposeReflection` of upper entries followed by the long Weyl
element on the right turns the opposite-cell parametrization into the transposed upper
unipotent matrices, and `measurePreserving_transposeReflection` keeps the measure.

The identity is proved by induction on `m`. In rank zero both measures have mass one. In the
induction step the maximal-parabolic integration formula of the Library
(`MaximalParabolicIntegration.integral_eq_chart`) separates the last row: the compact integral
is the positive chart constant `chartConstant m` times an integral over the last-row chart of
the compact integral of the Levi slice. The Levi slice is again smooth and modulus covariant
in rank `m` (`contMDiff_leviSlice`, `leviSlice_covariant`), and its determinant factor is one
on transposed unipotent arguments, so the induction hypothesis converts its compact integral
into an integral over `N_m`. The resulting iterated integral (last row, then the smaller
unipotent) is related to the ordered unipotent product of `unipotentProductMeasure_entryHaar`
by a linear change of the row variables with determinant one, which preserves Lebesgue
measure fiberwise; Fubini then gives the full integral over `N_(m+1)`. The new constant is
`chartConstant m · c`.

## Provenance

This is an internal result, the real counterpart of the Library's `ComplexModulusOpenCell`,
obtained from the maximal-parabolic integration formula
`MaximalParabolicIntegration.integral_eq_chart` by the induction above. It rewrites compact
integrals of modulus-covariant products as integrals over the opposite cell. The compact
pairing of principal-series vectors to which it is applied is the pairing defined by compact
Haar integration in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7; compact
projections of this kind are used in the rank induction of that paper, §8.2.
