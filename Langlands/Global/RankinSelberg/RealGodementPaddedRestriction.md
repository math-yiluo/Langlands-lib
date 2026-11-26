# Restriction of the real Godement coefficient to the padded group

This module is the real counterpart of the Library's `ComplexGodementPaddedRestriction`. It works
with the real Godement coefficient `RealJacquet.realAdjacentGodementCoefficient D a Φ U c` of
`RealAdjacentGodementRestriction`, the first-column Godement value `godementColumnValue` at
`w_{r+2} g`. Here `D` is a real quotient measure datum of rank `r`, `Φ` a Schwartz function on
`(r+1) × (r+2)` real matrices, `U` a function on `GL_{r+1}(ℝ)`, and `c` a real character datum.
`P g s = exp(s log|det g|)` is the determinant power.

A test `Φ` is *separated* by functions `F` on square matrices and `f` on column vectors when
`Φ([A | x]) = F(A) f(x)` for every square matrix `A` and last column `x`
(`joinLastColumn A x`). `realColumnProduct_joinLastColumn` records that the Library's separated
Schwartz test `realColumnProduct F f` satisfies this for Schwartz `F` and `f`.

* `columnMellin_restriction`: for a separated test, the weighted column Mellin integrand of the
  Godement value at `w_{r+2} diag(x, 1)`, evaluated at `k⁻¹ w_{r+1}`, equals
  `realAdjacentWeylSign r c` times the Library's restriction kernel
  `realAdjacentRestrictionKernel c.character F (realFourierTransform a f) U x k`.
* `integrable_restrictionKernel`: if `U` lies in `realUniformWhittakerModel r ds (-a)`, this
  restriction kernel is integrable for `D.groupHaar`. Its proof applies the Library's absolute
  convergence `realGodementColumnConvergence` to the translated test, transports it by the
  measure-preserving map `k ↦ k⁻¹ w_{r+1}`, and uses the previous identity, the Weyl sign being
  nonzero.
* `paddedRestrictionKernel c a F f U g b h =
  F(h b) · f̂_a(lastRow(g h⁻¹)) · U(g h⁻¹) · η(det h) · P h (r/2)`, where `f̂_a` is
  `realFourierTransform a f` and `η` the character of `c`.
* `restrictionKernel_change`: the substitution `k = g h⁻¹` turns the restriction kernel at `g b` into
  `η(det b) P b ((r+1)/2) P g (1/2)` times `paddedRestrictionKernel c a F f U g b h`.

`RealGodementPaddedRestrictionStatement` (proved by `realGodementPaddedRestriction`): for every
separated test `Φ` with factors `F`, `f`, every `U ∈ realUniformWhittakerModel r ds (-a)` and all
`g`, `b ∈ GL_{r+1}(ℝ)`, the padded kernel `paddedRestrictionKernel c a F f U g b` is integrable for
`D.groupHaar`, and

`realAdjacentGodementCoefficient D a Φ U c (diag(g b, 1)) =
realAdjacentWeylSign r c · η(det b) · P b ((r+1)/2) · P g (1/2) · ∫ paddedRestrictionKernel c a F f U g b h dh`.

The proof applies the Library's `realAdjacentGodementRestriction` at `g b` and changes variables by the
measure-preserving map `h ↦ g h⁻¹` (Haar measures on the real general linear group are unimodular,
`realMatrixHaar_symmetries`). Right multiplication by `diag(g, 1)` changes the leading square block of
the test argument and preserves its last column. The determinant characters cancel on the translated
factor and leave the half power of `det g`. This is the restriction to the padded group used in
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §§9.1 and 10.1.
